mod translation;

use std::{collections::HashMap, path::PathBuf};

use clap::StructOpt;
use color_eyre::{eyre::Context, Result};
use translation::translate_names;
use vcd::{IdCode, ScopeItem};

use crate::translation::translate_value;

#[derive(clap::Parser)]
struct CliArgs {
    infile: PathBuf,
    #[clap(short)]
    type_file: PathBuf,
    #[clap(short = 'o', default_value = "out.vcd")]
    outfile: PathBuf,
}

#[derive(Debug, Clone)]
struct MappedVar {
    pub raw: IdCode,
    pub parsed: IdCode,
    pub name: String,
}

type NewVarMap = HashMap<IdCode, Vec<MappedVar>>;

fn add_new_vars(
    mut result: NewVarMap,
    items: &Vec<ScopeItem>,
    writer: &mut vcd::Writer<impl std::io::Write>,
) -> Result<NewVarMap> {
    for item in items {
        match item {
            ScopeItem::Scope(scope) => {
                writer.scope_def(scope.scope_type, &scope.identifier)?;
                result = add_new_vars(result, &scope.children, writer)?;
                writer.upscope()?;
            }
            ScopeItem::Var(var) => {
                let raw = writer.add_var(var.var_type, var.size, &var.reference, var.index)?;
                let parsed = writer.add_var(
                    vcd::VarType::String,
                    1,
                    &format!("p_{}", var.reference),
                    None,
                )?;

                let new_map = MappedVar {
                    parsed,
                    raw,
                    name: var.reference.clone(),
                };

                result
                    .entry(var.code)
                    .or_insert(vec![])
                    .push(new_map.clone());
            }
        }
    }
    Ok(result)
}

fn main() -> Result<()> {
    color_eyre::install()?;

    let args = CliArgs::parse();

    let bytes = std::fs::read(&args.infile)?;
    let mut parser = vcd::Parser::new(std::io::Cursor::new(bytes));

    let header = parser
        .parse_header()
        .context("Failed to parse vcd header")?;

    let mut outbytes = vec![];
    let mut writer = vcd::Writer::new(&mut outbytes);

    match header.timescale {
        Some((t, unit)) => writer.timescale(t, unit)?,
        None => {}
    }
    let var_map = add_new_vars(HashMap::new(), &header.items, &mut writer)?;
    writer.enddefinitions()?;

    let type_file = std::fs::read_to_string(&args.type_file)
        .with_context(|| format!("Failed to read type file {:?}", args.type_file))?;

    let types = translate_names(
        ron::from_str(&type_file)
            .with_context(|| format!("failed to decode types in {:?}", args.type_file))?,
    );

    for command_result in parser {
        use vcd::Command::*;
        let command = command_result?;
        match command {
            ChangeScalar(id, value) => {
                for mapped in &var_map[&id] {
                    writer.change_scalar(mapped.raw, value)?;
                    if let Some(translated) = translate_value(&mapped.name, &[value], &types) {
                        writer.change_string(mapped.parsed, &translated)?;
                    }
                }
            }
            ChangeVector(id, value) => {
                for mapped in &var_map[&id] {
                    writer.change_vector(mapped.raw, &value)?;
                    if let Some(translated) = translate_value(&mapped.name, &value, &types) {
                        writer.change_string(mapped.parsed, &translated)?;
                    }
                }
            }
            ChangeReal(id, value) => {
                for mapped in &var_map[&id] {
                    writer.change_real(mapped.raw, value)?
                }
            }
            ChangeString(id, value) => {
                for mapped in &var_map[&id] {
                    writer.change_string(mapped.raw, &value)?
                }
            }
            other => writer.command(&other)?,
        }
    }

    std::fs::write(args.outfile, outbytes)?;

    Ok(())
}
