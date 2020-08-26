use crate::OpCode;

use std::collections::HashMap;

use anyhow::{anyhow, Result};
use parse_int::parse as parse_int;

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

enum Constant {
    String(String),
}

pub fn parse(input: String) -> Result<Vec<u8>> {
    let mut program = vec![];
    let mut label_values = HashMap::new();
    let mut labels_to_update = vec![];
    let mut constants = HashMap::new();

    let mut it = input.split_ascii_whitespace().peekable();
    it.next()
        .and_then(|token| (token == ".rodata:").to_option(()))
        .ok_or_else(|| anyhow!("Missing .rodata section"))?;

    while let Some(token) = it.next() {
        if token == ".code:" {
            break;
        }

        let constant_name = token
            .strip_suffix(':')
            .ok_or_else(|| anyhow!("missing `:` in constant declaration"))?;
        let constant_type = it.next().ok_or_else(|| anyhow!("Missing constant type"))?;
        let constant_value = it.next().ok_or_else(|| anyhow!("Missing contant value"))?;

        let constant = match constant_type {
            "string" => Constant::String(constant_value.to_string()),
            _ => return Err(anyhow!("Invalid constant type `{}`", constant_type)),
        };

        if constants.insert(constant_name, constant).is_some() {
            return Err(anyhow!("constant `{}` already declared", constant_name));
        }

        it.peek().ok_or_else(|| anyhow!("Missing .code section"))?;
    }

    while let Some(token) = it.next() {
        let token = token.to_lowercase();
        match token.as_ref() {
            "nop" => program.push(OpCode::Nop.into()),
            "add" => program.push(OpCode::Add.into()),
            "sub" => program.push(OpCode::Sub.into()),
            "mul" => program.push(OpCode::Mul.into()),
            "div" => program.push(OpCode::Div.into()),
            "mod" => program.push(OpCode::Mod.into()),
            "neg" => program.push(OpCode::Neg.into()),
            "inc" => program.push(OpCode::Inc.into()),
            "dec" => program.push(OpCode::Dec.into()),
            "eq" => program.push(OpCode::Equal.into()),
            "neq" => program.push(OpCode::NotEqual.into()),
            "gte" => program.push(OpCode::GreaterThanOrEqual.into()),
            "lte" => program.push(OpCode::LessThanOrEqual.into()),
            "gt" => program.push(OpCode::GreaterThan.into()),
            "lt" => program.push(OpCode::LessThan.into()),
            "push" => {
                program.push(OpCode::Push.into());
                let value = it.next().ok_or_else(|| anyhow!("Missing value to push"))?;
                let value = parse_int::<u64>(value)?;
                value.to_be_bytes().iter().for_each(|b| program.push(*b));
            }
            "pushsp" => program.push(OpCode::PushStackPointer.into()),
            "load" => program.push(OpCode::Load.into()),
            "store" => program.push(OpCode::Store.into()),
            "loadb" => program.push(OpCode::LoadByte.into()),
            "storeb" => program.push(OpCode::StoreByte.into()),
            "salloc" => program.push(OpCode::StackAlloc.into()),
            "call" => {
                program.push(OpCode::Call.into());

                let label = it.next().ok_or_else(|| anyhow!("Missing label to jump"))?;
                labels_to_update.push((label.to_string(), program.len()));

                0u64.to_be_bytes().iter().for_each(|b| program.push(*b));
            }
            "ret" => program.push(OpCode::Return.into()),
            "exit" => program.push(OpCode::Exit.into()),
            "print" => program.push(OpCode::Print.into()),
            "jump" => {
                program.push(OpCode::Jump.into());

                let label = it.next().ok_or_else(|| anyhow!("Missing label to jump"))?;
                labels_to_update.push((label.to_string(), program.len()));

                0u64.to_be_bytes().iter().for_each(|b| program.push(*b));
            }
            "condjump" => {
                program.push(OpCode::ConditionalJump.into());

                let label = it
                    .next()
                    .ok_or_else(|| anyhow!("Missing label to condjump"))?;
                labels_to_update.push((label.to_string(), program.len()));

                0u64.to_be_bytes().iter().for_each(|b| program.push(*b));
            }
            label if token.ends_with(':') => {
                let label = label.strip_suffix(':').unwrap();
                label_values.insert(label.to_string(), program.len());
            }
            _ => return Err(anyhow!("Invalid op code: {}", token)),
        }
    }

    for (label, i) in labels_to_update {
        label_values[&label]
            .to_be_bytes()
            .iter()
            .enumerate()
            .for_each(|(offset, b)| program[i + offset] = *b);
    }

    Ok(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{VirtualMachine, VirtualMachineState};

    #[test]
    fn test() {
        let program = "
    .rodata:
    .code:
        push 5
        call square
        exit
        
    square:
        salloc
        store
        pushsp
        load
        pushsp
        load
        mul
        ret"
        .to_string();

        let mut vm = VirtualMachine::new(parse(program).unwrap(), vec![]);
        while let Ok(state) = vm.step() {
            if let VirtualMachineState::Exit(result) = state {
                assert_eq!(result, 25);
                return;
            }
        }

        assert!(false);
    }
}
