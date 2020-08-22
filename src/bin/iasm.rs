use ivm::asm;

use anyhow::{anyhow, Result};
use clap::{App, Arg};

use std::fs;

fn main() -> Result<()> {
    let matches = App::new("iasm")
        .version("0.1.0")
        .author("Karim Elmougi <karim.elmougi@gmail.com>")
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
    let bitcode = asm::parse(program).map_err(|e| anyhow!("Invalid asm: {}", e))?;

    fs::write("out.bc", bitcode).map_err(|e| anyhow!("Unable to create bitcode file: {}", e))
}
