use spade_common::{
    location_info::{Loc, WithLocation},
    name::{Identifier, Path},
};
use spade_hir::symbol_table::{GenericArg, SymbolTable, Thing, TypeSymbol};

/// Add built in symbols like types to the symtab. The symbols are added with very high NameIDs to
/// not interfere with tests with hardcoded NameIDs
pub fn populate_symtab(symtab: &mut SymbolTable) {
    // Add primitive data types
    let mut id = std::u64::MAX;

    let mut add_type = |path: &[&str], args: Vec<Loc<GenericArg>>| {
        symtab.add_thing_with_id(
            id,
            Path::from_strs(path),
            Thing::Type(TypeSymbol::Declared(args).nowhere()),
        );
        id -= 1;
    };
    add_type(
        &["int"],
        vec![GenericArg::Number(Identifier("size".into())).nowhere()],
    );
    add_type(&["clk"], vec![]);
    add_type(&["bool"], vec![]);
}
