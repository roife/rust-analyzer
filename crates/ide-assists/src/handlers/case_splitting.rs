use std::iter;

use hir::{Adt, ImportPathConfig, ModuleDef};
use ide_db::{
    assists::ExprFillDefaultMode, helpers::mod_path_to_ast, syntax_helpers::suggest_name,
};

use itertools::Itertools;
use syntax::{
    SyntaxElement, ToSmolStr,
    ast::{
        self, AstNode, edit::IndentLevel, edit_in_place::Indent, make,
        syntax_factory::SyntaxFactory,
    },
};

use crate::{AssistContext, AssistId, Assists};

// Assist: split_match_arm
//
// Splits a match arm with a general pattern into multiple arms with more specific patterns.
//
// ```
// enum Result<T, E> { Ok(T), Err(E) }
// enum Option<T> { Some(T), None }
//
// fn handle(x: Result<Option<u32>, String>) {
//     match x {
//         Ok(res$0) => todo!(),
//         Err(err) => todo!(),
//     }
// }
// ```
// ->
// ```
// enum Result<T, E> { Ok(T), Err(E) }
// enum Option<T> { Some(T), None }
//
// fn handle(x: Result<Option<u32>, String>) {
//     match x {
//         Ok(Some(val)) => todo!(),
//         Ok(None) => todo!(),
//         Err(err) => todo!(),
//     }
// }
// ```
pub(crate) fn split_match_arm(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let match_arm = ctx.find_node_at_offset::<ast::MatchArm>()?;
    let match_arm_list = match_arm.syntax().parent().and_then(ast::MatchArmList::cast)?;
    let arm_idx = match_arm_list.arms().position(|arm| arm == match_arm)?;

    // Check if the arm has a guard - we don't support this for now
    if match_arm.guard().is_some() {
        return None;
    }

    let arm_pat = match_arm.pat()?;

    // Find the pattern to split at the cursor position
    let (pattern_to_split, replacement_context) = find_pattern_to_split(&arm_pat, ctx)?;

    // Generate the expanded patterns
    let enum_def = ctx.sema.type_of_pat(&pattern_to_split)?.adjusted().as_adt()?.as_enum()?;
    let module = ctx.sema.scope(pattern_to_split.syntax())?.module();
    let cfg = ctx.config.import_path_config();
    let expanded_patterns = generate_expanded_patterns(ctx, &enum_def, &module, cfg)?;
    if expanded_patterns.is_empty() {
        return None;
    }

    let target = pattern_to_split.syntax().text_range();

    acc.add(
        AssistId::refactor_rewrite("case_splitting"),
        "Case splitting on match arms",
        target,
        |builder| {
            let make = SyntaxFactory::with_mappings();

            // Create new arms for each expanded pattern
            let new_arms = expanded_patterns
                .into_iter()
                .map(|expanded_pat| {
                    let new_pattern = apply_pattern_replacement(
                        &arm_pat,
                        &pattern_to_split,
                        &expanded_pat,
                        &replacement_context,
                    );
                    let new_expr = match ctx.config.expr_fill_default {
                        ExprFillDefaultMode::Todo => make::ext::expr_todo(),
                        ExprFillDefaultMode::Underscore => make::ext::expr_underscore(),
                        ExprFillDefaultMode::Default => make::ext::expr_todo(),
                    };
                    make.match_arm(new_pattern, None, new_expr)
                })
                .collect_vec();

            let mut all_arms = match_arm_list.arms().collect_vec();
            all_arms.splice(arm_idx..arm_idx + 1, new_arms);

            let new_match_arm_list = make.match_arm_list(all_arms);

            // Get the proper indentation reference like add_missing_match_arms does
            let arm_list_range = match ctx.sema.original_range_opt(match_arm_list.syntax()) {
                Some(range) => range,
                None => return, // Can't get range, skip this transformation
            };
            let file = ctx.sema.parse(arm_list_range.file_id);
            let old_place = file.syntax().covering_element(arm_list_range.range);

            let old_place = match old_place {
                syntax::SyntaxElement::Node(it) => it,
                syntax::SyntaxElement::Token(it) => {
                    // If a token is found, it is '{' or '}'
                    // The parent is `{ ... }`
                    it.parent().expect("Token must have a parent.")
                }
            };

            new_match_arm_list.indent(IndentLevel::from_node(&old_place));

            let mut editor = builder.make_editor(&old_place);
            editor.replace(old_place, new_match_arm_list.syntax());
            editor.add_mappings(make.take());
            builder.add_file_edits(ctx.vfs_file_id(), editor);
        },
    )
}

#[derive(Debug)]
enum ReplacementContext {
    /// Direct replacement - the pattern to split is the entire arm pattern
    Direct,
    /// Nested replacement - the pattern is inside a tuple struct pattern
    TupleStruct { outer_path: ast::Path, field_index: usize, total_fields: usize },
    /// Nested replacement - the pattern is inside a record pattern
    Record { outer_path: ast::Path, field_name: String },
}

fn find_pattern_to_split(
    arm_pat: &ast::Pat,
    ctx: &AssistContext<'_>,
) -> Option<(ast::Pat, ReplacementContext)> {
    let ident_pat = ctx.find_node_at_offset::<ast::IdentPat>()?;
    // Check if the cursor is on the pattern of the arm
    if !arm_pat.syntax().text_range().contains(ctx.offset()) {
        return None;
    }

    let adt = ctx.sema.type_of_binding_in_pat(&ident_pat)?.as_adt()?;
    if !matches!(adt, Adt::Enum(_)) {
        return None;
    }

    let context = find_replacement_context(&ident_pat, arm_pat)?;
    Some((ident_pat.into(), context))
}

fn find_replacement_context(
    ident_pat: &ast::IdentPat,
    arm_pat: &ast::Pat,
) -> Option<ReplacementContext> {
    // Walk up from the ident_pat to find how it's nested
    let mut current = ident_pat.syntax().parent()?;

    loop {
        if let Some(tuple_struct_pat) = ast::TupleStructPat::cast(current.clone()) {
            if let Some(path) = tuple_struct_pat.path() {
                // Find which field position this ident_pat is in
                let fields: Vec<_> = tuple_struct_pat.fields().collect_vec();
                if let Some(field_index) = fields.iter().position(|field| {
                    field.syntax().descendants().any(|descendant| descendant == *ident_pat.syntax())
                }) {
                    return Some(ReplacementContext::TupleStruct {
                        outer_path: path,
                        field_index,
                        total_fields: fields.len(),
                    });
                }
            }
        }

        if let Some(record_pat) = ast::RecordPat::cast(current.clone()) {
            if let Some(path) = record_pat.path() {
                // Find which field this ident_pat belongs to
                if let Some(field_list) = record_pat.record_pat_field_list() {
                    for field in field_list.fields() {
                        if let Some(field_pat) = field.pat() {
                            if field_pat
                                .syntax()
                                .descendants()
                                .any(|descendant| descendant == *ident_pat.syntax())
                            {
                                if let Some(name_ref) = field.name_ref() {
                                    return Some(ReplacementContext::Record {
                                        outer_path: path,
                                        field_name: name_ref.text().to_string(),
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }

        if current == *arm_pat.syntax() {
            return Some(ReplacementContext::Direct);
        }

        current = current.parent()?;
    }
}

fn generate_expanded_patterns(
    ctx: &AssistContext<'_>,
    enum_def: &hir::Enum,
    module: &hir::Module,
    cfg: ImportPathConfig,
) -> Option<Vec<ast::Pat>> {
    let db = ctx.db();
    let edition = module.krate().edition(db);
    let make = SyntaxFactory::with_mappings();

    let mut patterns = Vec::new();

    for variant in enum_def.variants(db) {
        let path = mod_path_to_ast(&module.find_path(db, ModuleDef::from(variant), cfg)?, edition);

        let fields = variant.fields(db);
        let pat = match variant.kind(db) {
            hir::StructKind::Tuple => {
                let mut name_generator = suggest_name::NameGenerator::default();
                let pats = fields.into_iter().enumerate().map(|(i, f)| {
                    let name = name_generator
                        .for_type(&f.ty(db), db, edition)
                        .unwrap_or_else(|| format!("_{i}").to_smolstr());
                    make::ext::simple_ident_pat(make.name(&name)).into()
                });
                make.tuple_struct_pat(path, pats).into()
            }
            hir::StructKind::Record => {
                let fields = fields
                    .into_iter()
                    .map(|f| make.ident_pat(false, false, make.name(f.name(db).as_str())))
                    .map(|ident| make.record_pat_field_shorthand(ident.into()));
                let fields = make.record_pat_field_list(fields, None);
                make.record_pat_with_fields(path, fields).into()
            }
            hir::StructKind::Unit => make.path_pat(path),
        };

        patterns.push(pat);
    }

    Some(patterns)
}

fn apply_pattern_replacement(
    original_arm_pat: &ast::Pat,
    _pattern_to_replace: &ast::Pat,
    replacement_pattern: &ast::Pat,
    context: &ReplacementContext,
) -> ast::Pat {
    match context {
        ReplacementContext::Direct => replacement_pattern.clone(),
        ReplacementContext::TupleStruct { outer_path, field_index, total_fields } => {
            // Create a new tuple struct pattern with the replacement at the right position
            let make = SyntaxFactory::with_mappings();
            let mut new_fields = Vec::new();

            // Extract the original fields from the original pattern
            if let ast::Pat::TupleStructPat(original_tuple_pat) = original_arm_pat {
                if let Some(original_path) = original_tuple_pat.path() {
                    if original_path.to_string() == outer_path.to_string() {
                        let original_fields = original_tuple_pat.fields().collect_vec();
                        for i in 0..*total_fields {
                            if i == *field_index {
                                new_fields.push(replacement_pattern.clone());
                            } else if i < original_fields.len() {
                                new_fields.push(original_fields[i].clone());
                            } else {
                                new_fields.push(make.wildcard_pat().into());
                            }
                        }
                    }
                }
            }

            // If we couldn't extract original fields, fall back to wildcards
            if new_fields.is_empty() {
                for i in 0..*total_fields {
                    if i == *field_index {
                        new_fields.push(replacement_pattern.clone());
                    } else {
                        new_fields.push(make.wildcard_pat().into());
                    }
                }
            }

            make.tuple_struct_pat(outer_path.clone(), new_fields).into()
        }
        ReplacementContext::Record { outer_path, field_name } => {
            // Create a new record pattern with the replacement field
            let make = SyntaxFactory::with_mappings();
            let field =
                make.record_pat_field(make.name_ref(field_name), replacement_pattern.clone());
            let field_list = make.record_pat_field_list(iter::once(field), Some(make.rest_pat()));
            make.record_pat_with_fields(outer_path.clone(), field_list).into()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    #[test]
    fn test_split_simple_option() {
        check_assist(
            split_match_arm,
            r#"
//- minicore: option
fn main() {
    let x: Option<Option<i32>> = Some(Some(42));
    match x {
        Some(inner$0) => todo!(),
        None => todo!(),
    }
}
"#,
            r#"
fn main() {
    let x: Option<Option<i32>> = Some(Some(42));
    match x {
        Some(Some(val)) => todo!(),
        Some(None) => todo!(),
        None => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_split_result_ok() {
        check_assist(
            split_match_arm,
            r#"
//- minicore: option, result
fn main() {
    let x: Result<Option<i32>, ()> = Ok(Some(42));
    match x {
        Ok(res$0) => todo!(),
        Err(err) => todo!(),
    }
}
"#,
            r#"
fn main() {
    let x: Result<Option<i32>, ()> = Ok(Some(42));
    match x {
        Ok(Some(val)) => todo!(),
        Ok(None) => todo!(),
        Err(err) => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_split_option_some() {
        check_assist(
            split_match_arm,
            r#"
//- minicore: option, result
fn main() {
    let x: Option<Result<i32, ()>> = Some(Ok(42));
    match x {
        Some(res$0) => todo!(),
        None => todo!(),
    }
}
"#,
            r#"
fn main() {
    let x: Option<Result<i32, ()>> = Some(Ok(42));
    match x {
    Some(Ok(val)) => todo!(),
    Some(Err(val)) => todo!(),
    None => todo!(),
}
}
"#,
        );
    }

    #[test]
    fn test_split_custom_enum_tuple_struct() {
        check_assist(
            split_match_arm,
            r#"
enum MyEnum { A(bool), B(i32), C }
fn main() {
    let x: MyEnum = MyEnum::A(true);
    match x {
        MyEnum::A(inner$0) => todo!(),
        _ => todo!(),
    }
}
"#,
            r#"
enum MyEnum { A(bool), B(i32), C }
fn main() {
    let x: MyEnum = MyEnum::A(true);
    match x {
        MyEnum::A(true) => todo!(),
        MyEnum::A(false) => todo!(),
        _ => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_split_custom_enum_record_struct() {
        check_assist(
            split_match_arm,
            r#"
enum Color { Red, Green, Blue }
enum Shape { Circle { radius: f64, color: Color }, Square { side: f64 } }
fn main() {
    let shape = Shape::Circle { radius: 1.0, color: Color::Red };
    match shape {
        Shape::Circle { color: c$0, .. } => todo!(),
        _ => todo!(),
    }
}
"#,
            r#"
enum Color { Red, Green, Blue }
enum Shape { Circle { radius: f64, color: Color }, Square { side: f64 } }
fn main() {
    let shape = Shape::Circle { radius: 1.0, color: Color::Red };
    match shape {
        Shape::Circle { color: Color::Red, .. } => todo!(),
        Shape::Circle { color: Color::Green, .. } => todo!(),
        Shape::Circle { color: Color::Blue, .. } => todo!(),
        _ => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_split_deeply_nested() {
        check_assist(
            split_match_arm,
            r#"
//- minicore: option
enum MyEnum { X(Option<bool>), Y }
fn main() {
    let x: Option<MyEnum> = Some(MyEnum::X(Some(true)));
    match x {
        Some(MyEnum::X(inner$0)) => todo!(),
        _ => todo!(),
    }
}
"#,
            r#"
enum MyEnum { X(Option<bool>), Y }
fn main() {
    let x: Option<MyEnum> = Some(MyEnum::X(Some(true)));
    match x {
        MyEnum::X(Some(val)) => todo!(),
        MyEnum::X(None) => todo!(),
        _ => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_not_applicable_non_enum_type() {
        check_assist_not_applicable(
            split_match_arm,
            r#"
fn main() {
    let x: i32 = 42;
    match x {
        val$0 => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_not_applicable_struct_type() {
        check_assist_not_applicable(
            split_match_arm,
            r#"
struct Point { x: i32, y: i32 }
fn main() {
    let p = Point { x: 1, y: 2 };
    match p {
        Point { x: val$0, y: _ } => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_not_applicable_single_variant_enum() {
        check_assist_not_applicable(
            split_match_arm,
            r#"
enum Single { Only(i32) }
fn main() {
    let x = Single::Only(42);
    match x {
        Single::Only(val$0) => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_split_with_explicit_path() {
        check_assist(
            split_match_arm,
            r#"
mod inner {
    pub enum Status { Ready(bool), Waiting }
}
fn main() {
    let status = inner::Status::Ready(true);
    match status {
        inner::Status::Ready(ready$0) => todo!(),
        inner::Status::Waiting => todo!(),
    }
}
"#,
            r#"
mod inner {
    pub enum Status { Ready(bool), Waiting }
}
fn main() {
    let status = inner::Status::Ready(true);
    match status {
        inner::Status::Ready(true) => todo!(),
        inner::Status::Ready(false) => todo!(),
        inner::Status::Waiting => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_split_preserves_other_arms_order() {
        check_assist(
            split_match_arm,
            r#"
//- minicore: option
fn main() {
    let x: Option<bool> = Some(true);
    match x {
        None => println!("none"),
        Some(val$0) => todo!(),
    }
}
"#,
            r#"
fn main() {
    let x: Option<bool> = Some(true);
    match x {
        None => println!("none"),
        Some(true) => todo!(),
        Some(false) => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_split_mixed_variant_types() {
        check_assist(
            split_match_arm,
            r#"
enum Message {
    Text(String),
    Number(i32),
    Flag(bool),
    Empty,
}
fn main() {
    let msg = Message::Flag(true);
    match msg {
        Message::Flag(flag$0) => todo!(),
        _ => todo!(),
    }
}
"#,
            r#"
enum Message {
    Text(String),
    Number(i32),
    Flag(bool),
    Empty,
}
fn main() {
    let msg = Message::Flag(true);
    match msg {
        Message::Flag(true) => todo!(),
        Message::Flag(false) => todo!(),
        _ => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_not_applicable_already_expanded() {
        check_assist_not_applicable(
            split_match_arm,
            r#"
//- minicore: option
fn main() {
    let x: Option<bool> = Some(true);
    match x {
        Some(true$0) => todo!(),
        Some(false) => todo!(),
        None => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_split_with_import() {
        check_assist(
            split_match_arm,
            r#"
//- minicore: option
fn main() {
    let x: Option<bool> = Some(true);
    match x {
        Some(val$0) => todo!(),
        None => todo!(),
    }
}
"#,
            r#"
fn main() {
    let x: Option<bool> = Some(true);
    match x {
        Some(true) => todo!(),
        Some(false) => todo!(),
        None => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_not_applicable_cursor_not_on_binding() {
        check_assist_not_applicable(
            split_match_arm,
            r#"
//- minicore: option
fn main() {
    let x: Option<bool> = Some(true);
    match x {
        $0Some(val) => todo!(),
        None => todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_not_applicable_on_wildcard() {
        check_assist_not_applicable(
            split_match_arm,
            r#"
//- minicore: option
fn main() {
    let x: Option<i32> = Some(42);
    match x {
        _ $0=> todo!(),
    }
}
"#,
        );
    }

    #[test]
    fn test_not_applicable_with_guard() {
        check_assist_not_applicable(
            split_match_arm,
            r#"
//- minicore: option
fn main() {
    let x: Option<i32> = Some(42);
    match x {
        Some(val$0) if val > 10 => todo!(),
        _ => todo!(),
    }
}
"#,
        );
    }
}
