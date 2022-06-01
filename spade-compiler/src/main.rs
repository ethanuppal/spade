use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use anyhow::{anyhow, Context, Result};
use clap::Parser;
use codespan_reporting::term::termcolor::Buffer;

#[derive(Parser)]
#[structopt(name = "spade", about = "Compiler for the spade language")]
pub struct Opt {
    #[structopt(name = "INPUT_FILE")]
    pub infile: PathBuf,
    #[structopt(name = "EXTRA_FILES")]
    pub extra_files: Vec<PathBuf>,
    #[structopt(short = 'o')]
    pub outfile: PathBuf,
    /// File to output the MIR for the generated modules. Primarily for debug purposes
    #[structopt(long)]
    pub mir_output: Option<PathBuf>,
    /// Do not include color in the error report
    #[structopt(long = "no-color")]
    pub no_color: bool,

    /// Write a mapping between expression ids/names and the types of the values
    /// formatted in ron https://github.com/ron-rs/ron
    #[structopt(long)]
    pub type_dump: Option<PathBuf>,

    /// Print a traceback of the type inference process if type inference or hir lowering fails
    #[structopt(long = "print-type-traceback")]
    pub print_type_traceback: bool,
    /// Print a traceback of the parser if parsing fails
    #[structopt(long = "print-parse-traceback")]
    pub print_parse_traceback: bool,
}

fn main() -> Result<()> {
    let mut opts = Opt::parse();

    let mut infiles = vec![opts.infile.clone()];
    infiles.append(&mut opts.extra_files);

    let sources: Result<Vec<(String, String)>> = infiles
        .into_iter()
        .map(|infile| {
            let mut file = File::open(&infile)
                .with_context(|| format!("Failed to open {}", &infile.to_string_lossy()))?;
            let mut file_content = String::new();
            file.read_to_string(&mut file_content)?;
            Ok((infile.to_string_lossy().to_string(), file_content))
        })
        .collect();

    let mut buffer = if opts.no_color {
        Buffer::no_color()
    } else {
        Buffer::ansi() // FIXME: Use `Buffer::console()` on windows?
    };

    let spade_opts = spade::Opt {
        error_buffer: &mut buffer,
        outfile: Some(opts.outfile),
        mir_output: opts.mir_output,
        type_dump_file: opts.type_dump,
        print_type_traceback: opts.print_type_traceback,
        print_parse_traceback: opts.print_parse_traceback,
    };

    match spade::compile(sources?, spade_opts) {
        Ok(_) => Ok(()),
        Err(_) => {
            std::io::stderr().write_all(buffer.as_slice())?;
            Err(anyhow!("aborting due to previous error"))
        }
    }
}
