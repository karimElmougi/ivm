use crate::OpCode;
use crate::ROM_ADDRESS_MASK;

use std::collections::HashMap;

use anyhow::{anyhow, Result};
use parse_int::parse as parse_int;
use pest::Parser;

trait ToOption {
    fn to_option<T>(self, t: T) -> Option<T>;
}

impl ToOption for bool {
    fn to_option<T>(self, t: T) -> Option<T> {
        if self {
            Some(t)
        } else {
            None
        }
    }
}

#[derive(Parser)]
#[grammar = "iasm.pest"]
struct IASMParser;

pub fn parse(input: String) -> Result<(Vec<u8>, Vec<u8>)> {
    let mut pairs = IASMParser::parse(Rule::program, &input)?;

    let rodata = pairs.next().unwrap();
    let constants = parse_constants(rodata)?;

    let code = pairs.next().unwrap();
    parse_instructions(code, constants)
}

fn parse_constants(rodata: pest::iterators::Pair<Rule>) -> Result<HashMap<String, String>> {
    let mut constants = HashMap::new();
    let it = rodata.into_inner();
    for constant in it {
        let mut inner = constant.into_inner();

        let name = inner.next().unwrap().as_str();
        let constant_type = inner.next().unwrap().as_str();
        let value = inner.next().unwrap().as_str();

        match constant_type {
            "string" => (),
            _ => return Err(anyhow!("Invalid constant type: {}", constant_type)),
        }

        if constants
            .insert(name.to_string(), (value[1..value.len() - 1]).to_string())
            .is_some()
        {
            return Err(anyhow!("constant `{}` already declared", name));
        }
    }

    Ok(constants)
}

fn parse_instructions(
    code: pest::iterators::Pair<Rule>,
    constants: HashMap<String, String>,
) -> Result<(Vec<u8>, Vec<u8>)> {
    let mut program = vec![];
    let mut label_values = HashMap::new();
    let mut labels_to_update = vec![];

    for instruction in code.into_inner() {
        let rule_components = instruction.into_inner();
        for component in rule_components {
            match component.as_rule() {
                Rule::nop => program.push(OpCode::Nop.into()),
                Rule::add => program.push(OpCode::Add.into()),
                Rule::sub => program.push(OpCode::Sub.into()),
                Rule::mul => program.push(OpCode::Mul.into()),
                Rule::div => program.push(OpCode::Div.into()),
                Rule::modulus => program.push(OpCode::Mod.into()),
                Rule::neg => program.push(OpCode::Neg.into()),
                Rule::inc => program.push(OpCode::Inc.into()),
                Rule::dec => program.push(OpCode::Dec.into()),
                Rule::eq => program.push(OpCode::Equal.into()),
                Rule::neq => program.push(OpCode::NotEqual.into()),
                Rule::gte => program.push(OpCode::GreaterThanOrEqual.into()),
                Rule::lte => program.push(OpCode::LessThanOrEqual.into()),
                Rule::gt => program.push(OpCode::GreaterThan.into()),
                Rule::lt => program.push(OpCode::LessThan.into()),
                Rule::pushsp => program.push(OpCode::PushStackPointer.into()),
                Rule::load => program.push(OpCode::Load.into()),
                Rule::store => program.push(OpCode::Store.into()),
                Rule::loadb => program.push(OpCode::LoadByte.into()),
                Rule::storeb => program.push(OpCode::StoreByte.into()),
                Rule::alloca => program.push(OpCode::StackAlloc.into()),
                Rule::ret => program.push(OpCode::Return.into()),
                Rule::exit => program.push(OpCode::Exit.into()),
                Rule::print => program.push(OpCode::Print.into()),
                Rule::jump => {
                    program.push(OpCode::Jump.into());

                    let label = component.into_inner().next().unwrap().as_str();
                    labels_to_update.push((label.to_string(), program.len()));

                    0u64.to_be_bytes().iter().for_each(|b| program.push(*b));
                }
                Rule::condjump => {
                    program.push(OpCode::ConditionalJump.into());

                    let label = component.into_inner().next().unwrap().as_str();
                    labels_to_update.push((label.to_string(), program.len()));

                    0u64.to_be_bytes().iter().for_each(|b| program.push(*b));
                }
                Rule::call => {
                    program.push(OpCode::Call.into());

                    let label = component.into_inner().next().unwrap().as_str();
                    labels_to_update.push((label.to_string(), program.len()));

                    0u64.to_be_bytes().iter().for_each(|b| program.push(*b));
                }
                Rule::push => {
                    program.push(OpCode::Push.into());

                    let value = component.into_inner().next().unwrap().as_str();
                    let value = if value.starts_with('-') {
                        parse_int::<i64>(value)? as u64
                    } else {
                        match parse_int::<u64>(value) {
                            Ok(value) => value,
                            Err(_) => {
                                labels_to_update.push((value.to_string(), program.len()));
                                0u64
                            }
                        }
                    };

                    value.to_be_bytes().iter().for_each(|b| program.push(*b));
                }
                Rule::label => {
                    let label = component.into_inner().next().unwrap().as_str();
                    label_values.insert(label.to_string(), program.len());
                }
                _ => return Err(anyhow!("Invalid op code: `{}`", component.as_str())),
            }
        }
    }

    let mut rodata = vec![];
    for (label, value) in constants {
        let address = ROM_ADDRESS_MASK | rodata.len();
        label_values.insert(label, address);

        for byte in value.as_bytes() {
            rodata.push(*byte);
        }
        rodata.push(0);
    }

    for (label, i) in labels_to_update {
        label_values[&label]
            .to_be_bytes()
            .iter()
            .enumerate()
            .for_each(|(offset, b)| program[i + offset] = *b);
    }

    Ok((program, rodata))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{VirtualMachine, VirtualMachineState};

    #[test]
    fn test() -> Result<()> {
        let program = "
    .rodata:
    .code:
        push 5
        call square
        exit
        
    square:
        alloca
        store
        pushsp
        load
        pushsp
        load
        mul
        ret"
        .to_string();

        let (program, rodata) = parse(program)?;
        let mut vm = VirtualMachine::new(program, rodata);

        while let Ok(state) = vm.step() {
            if let VirtualMachineState::Exit(result) = state {
                assert_eq!(result, 25);
                return Ok(());
            }
        }

        Err(anyhow!("VM encountered an error"))
    }

    #[test]
    fn print_test() -> Result<()> {
        let program = "
    .rodata: 
        hello: string = \"hello, world!\n\"
        hey: string = \"heyo\"
    .code:
        push hello
        print
        exit"
            .to_string();

        let (program, rodata) = parse(program)?;
        let mut vm = VirtualMachine::new(program, rodata);

        while let Ok(VirtualMachineState::Running) = vm.step() {}

        Ok(())
    }
}
