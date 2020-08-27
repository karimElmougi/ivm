use ivm::asm;

use anyhow::{anyhow, Result};
use clap::{App, Arg};

use std::fs;

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() -> Result<()> {
    let matches = App::new("iasm")
        .version(VERSION)
        .about("Parses a given ivm assembler file into bitcode")
        .arg(
            Arg::with_name("file")
                .value_name("FILE")
                .required(true)
                .help("iasm file"),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .help("output path of the bitcode file"),
        )
        .get_matches();

    let file_path = matches.value_of("file").unwrap();

    let program = fs::read_to_string(file_path)
        .map_err(|e| anyhow!("Unable to read file {}: {}", file_path, e))?;

    let (mut bitcode, mut rodata) =
        asm::parse(program).map_err(|e| anyhow!("Invalid asm: {}", e))?;

    let mut file_content = vec![];
    rodata.len().to_be_bytes().iter().for_each(|b| file_content.push(*b));
    file_content.append(&mut rodata);
    file_content.append(&mut bitcode);

    fs::write("out.bc", file_content).map_err(|e| anyhow!("Unable to create bitcode file: {}", e))
}
