use crate::OpCode;

use std::collections::HashMap;

use anyhow::{anyhow, Result};
use parse_int::parse as parse_int;

pub fn parse(input: String) -> Result<Vec<u8>> {
    let mut program = vec![];
    let mut label_values = HashMap::new();
    let mut labels_to_update = vec![];

    let mut it = input.split_ascii_whitespace();
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
    use crate::VirtualMachine;

    #[test]
    fn test() {
        let program = "
        push 1
        push 2
        add
        push 4
        mul
        push 0x2
        div
        neg
        jump label
        push 999
  label:
        push 1
        add"
        .to_string();

        let mut vm = VirtualMachine::new(parse(program).unwrap());
        while let Ok(_) = vm.step() {}

        assert_eq!(*vm.stack.last().unwrap() as i64, -5);
    }
}
