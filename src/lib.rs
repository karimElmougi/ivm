use std::convert::TryFrom;
use std::fmt::{self, Display};
use std::io::{self, Read};

#[macro_use]
extern crate static_assertions;
use anyhow::{anyhow, Result};
use byteorder::{BigEndian, ReadBytesExt};
use num_enum::{IntoPrimitive, TryFromPrimitive};
use num_traits::PrimInt;

const_assert_eq!(std::mem::size_of::<usize>(), std::mem::size_of::<u64>());

struct VirtualMachine {
    program_counter: Cursor<u8>,
    stack: Vec<u64>,
    heap: Vec<u8>,
}

impl VirtualMachine {
    fn new(program: Vec<u8>) -> Self {
        Self {
            program_counter: Cursor::new(program),
            stack: Default::default(),
            heap: Default::default(),
        }
    }

    fn step(&mut self) -> Result<()> {
        let op_code = self
            .program_counter
            .read_u8()
            .map_err(|_| anyhow!("Reached end of program"))?;
        let op_code =
            OpCode::try_from(op_code).map_err(|_| anyhow!("Invalid OP code: {}", op_code))?;

        match op_code {
            OpCode::Add => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push(op1 + op2);
            }
            OpCode::Sub => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push(op1 - op2);
            }
            OpCode::Mul => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push(op1 * op2);
            }
            OpCode::Div => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push(op1 / op2);
            }
            OpCode::Equal => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push((op1 == op2) as u64);
            }
            OpCode::NotEqual => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push((op1 != op2) as u64);
            }
            OpCode::GreaterThanOrEqual => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push((op1 >= op2) as u64);
            }
            OpCode::LessThanOrEqual => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push((op1 <= op2) as u64);
            }
            OpCode::GreaterThan => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push((op1 > op2) as u64);
            }
            OpCode::LessThan => {
                let (op1, op2) = self.pop_stack_2()?;
                self.stack.push((op1 < op2) as u64);
            }
            OpCode::Push => {
                let value = self
                    .program_counter
                    .read_u64::<BigEndian>()
                    .map_err(|_| anyhow!("Reached end of program mid instruction"))?;
                self.stack.push(value);
            }
            // OpCode::Load => {
            // }
            // OpCode::Store => {
            // }
            // OpCode::Return => {
            // }
            _ => unimplemented!("{}", op_code),
        }

        Ok(())
    }

    fn pop_stack(&mut self) -> Result<u64> {
        self.stack.pop().ok_or_else(|| anyhow!("Stack Underflow"))
    }

    fn pop_stack_2(&mut self) -> Result<(u64, u64)> {
        self.stack
            .pop()
            .and_then(|op2| self.stack.pop().and_then(|op1| Some((op1, op2))))
            .ok_or_else(|| anyhow!("Stack Underflow"))
    }

    fn alloc(&mut self) -> usize {
        let size = self.stack.pop().expect("Stack Underflow");
        self.heap.len()
    }
}

struct Cursor<I>
where
    I: PrimInt,
{
    program: Immutable<Vec<I>>,
    begin: *const I,
    end: *const I,
    cursor: *const I,
}

impl<I> Cursor<I>
where
    I: PrimInt,
{
    fn new(program: Vec<I>) -> Self {
        let begin = program.as_ptr();
        let end = unsafe { begin.add(program.len()) };
        Self {
            program: Immutable::new(program),
            begin,
            end,
            cursor: begin,
        }
    }

    fn next(&mut self) -> Option<I> {
        if self.cursor != self.end {
            let value = unsafe { *self.cursor };
            self.cursor = unsafe { self.cursor.add(1) };
            Some(value)
        } else {
            None
        }
    }

    fn go_to(&mut self, pos: usize) -> Result<()> {
        let new_cursor = unsafe { self.begin.add(pos) };
        if new_cursor < self.end {
            self.cursor = new_cursor;
            Ok(())
        } else {
            Err(anyhow!("Position out of bounds"))
        }
    }
}

impl Read for Cursor<u8> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut num_read = 0;
        for (i, byte) in buf.iter_mut().enumerate() {
            match self.next() {
                Some(val) => *byte = val,
                None => return Ok(i),
            }
            num_read = i + 1;
        }
        Ok(num_read)
    }
}

struct Immutable<T>(T);

impl<T> Immutable<T> {
    fn new(t: T) -> Self {
        Self(t)
    }

    fn as_ref(&self) -> &T {
        &self.0
    }
}

#[derive(TryFromPrimitive, IntoPrimitive, Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
enum OpCode {
    Add,
    Sub,
    Mul,
    Div,
    Equal,
    NotEqual,
    GreaterThanOrEqual,
    LessThanOrEqual,
    GreaterThan,
    LessThan,
    Push,
    Load,
    Store,
    Return,
}

impl Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_ops() {
        let mut program = vec![];

        program.push(OpCode::Push.into());
        1u64.to_be_bytes().iter().for_each(|b| program.push(*b));

        program.push(OpCode::Push.into());
        2u64.to_be_bytes().iter().for_each(|b| program.push(*b));

        program.push(OpCode::Add.into());

        program.push(OpCode::Push.into());
        4u64.to_be_bytes().iter().for_each(|b| program.push(*b));

        program.push(OpCode::Mul.into());

        program.push(OpCode::Push.into());
        2u64.to_be_bytes().iter().for_each(|b| program.push(*b));

        program.push(OpCode::Div.into());

        let mut vm = VirtualMachine::new(program);
        while let Ok(_) = vm.step() {}

        assert_eq!(*vm.stack.last().unwrap(), 6);
    }
}
