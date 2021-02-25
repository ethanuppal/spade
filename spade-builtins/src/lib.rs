use spade_ast_lowering::symbol_table::{SymbolTable, Thing, TypeSymbol};
use spade_common::location_info::WithLocation;
use spade_parser::ast::Path;
use spade_types::BaseType;

/// Add built in symbols like types to the symtab. The symbols are added with very high NameIDs to
/// not interfere with tests with hardcoded NameIDs
pub fn populate_symtab(symtab: &mut SymbolTable) {
    // Add primitive data types
    let mut id = std::u64::MAX;

    let mut add_type = |path: &str, t: BaseType| {
        symtab.add_thing_with_id(
            id,
            Path::from_strs(&[path]),
            Thing::Type(TypeSymbol::Alias(t.nowhere())),
        );
        id -= 1;
    };
    add_type("int", BaseType::Int);
    add_type("clk", BaseType::Clock);
    add_type("bool", BaseType::Bool);
}
