pub mod asm;
pub mod mem;
pub mod op_code;

use mem::{size_in_bits, Address, Allocation, Cursor, StackFrame, ValueStack};
use op_code::OpCode;

use std::collections::BTreeMap;
use std::convert::{TryFrom, TryInto};

#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate static_assertions;
use anyhow::{anyhow, Result};
use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};

const_assert_eq!(std::mem::size_of::<usize>(), std::mem::size_of::<u64>());

pub enum VirtualMachineState {
    Running,
    Exit(i64),
}

pub struct VirtualMachine {
    program_counter: Cursor<u8>,
    value_stack: ValueStack,
    stack: Vec<StackFrame>,
    heap: Vec<u8>,
    rodata: Vec<u8>,
    allocations: BTreeMap<usize, Allocation>,
}

impl VirtualMachine {
    pub fn new(program: Vec<u8>, rodata: Vec<u8>) -> Self {
        Self {
            program_counter: Cursor::new(program),
            value_stack: Default::default(),
            stack: vec![StackFrame::new(0)],
            heap: Default::default(),
            rodata,
            allocations: Default::default(),
        }
    }

    pub fn step(&mut self) -> Result<VirtualMachineState> {
        let op_code = self
            .program_counter
            .read_u8()
            .map_err(|_| anyhow!("Reached end of program"))?;

        let op_code =
            OpCode::try_from(op_code).map_err(|_| anyhow!("Invalid OP code: {}", op_code))?;

        match op_code {
            OpCode::Nop => {}
            OpCode::Add => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push(op1 + op2);
            }
            OpCode::Sub => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push(op1 - op2);
            }
            OpCode::Mul => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push(op1 * op2);
            }
            OpCode::Div => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push(op1 / op2);
            }
            OpCode::Mod => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push(op1 % op2);
            }
            OpCode::Neg => {
                let value = self.value_stack.pop()?;
                self.value_stack.push(-(value as i64) as u64);
            }
            OpCode::Inc => {
                let value = self.value_stack.pop()?;
                self.value_stack.push(value + 1);
            }
            OpCode::Dec => {
                let value = self.value_stack.pop()?;
                self.value_stack.push(value - 1);
            }
            OpCode::Equal => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push((op1 == op2) as u64);
            }
            OpCode::NotEqual => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push((op1 != op2) as u64);
            }
            OpCode::GreaterThanOrEqual => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push((op1 >= op2) as u64);
            }
            OpCode::LessThanOrEqual => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push((op1 <= op2) as u64);
            }
            OpCode::GreaterThan => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push((op1 > op2) as u64);
            }
            OpCode::LessThan => {
                let (op1, op2) = self.value_stack.pop_2()?;
                self.value_stack.push((op1 < op2) as u64);
            }
            OpCode::Push => {
                let value = self
                    .program_counter
                    .read_u64::<BigEndian>()
                    .map_err(|_| anyhow!("Reached end of program mid instruction"))?;

                self.value_stack.push(value);
            }
            OpCode::PushStackPointer => {
                self.value_stack
                    .push(Address::Stack(self.stack.len() - 1, 0).into());
            }
            OpCode::Jump => {
                let address = self
                    .program_counter
                    .read_u64::<BigEndian>()
                    .map_err(|_| anyhow!("Reached end of program mid instruction"))?
                    as usize;

                self.program_counter.go_to(address)?;
            }
            OpCode::ConditionalJump => {
                let address = self
                    .program_counter
                    .read_u64::<BigEndian>()
                    .map_err(|_| anyhow!("Reached end of program mid instruction"))?
                    as usize;

                let condition = self.value_stack.pop()?;
                if condition != 0 {
                    self.program_counter.go_to(address as usize)?;
                }
            }
            OpCode::Call => {
                if self.stack.len() == usize::MAX << size_in_bits::<u8>() {
                    return Err(anyhow!("Stack overflow"));
                }

                let call_address = self
                    .program_counter
                    .read_u64::<BigEndian>()
                    .map_err(|_| anyhow!("Reached end of program mid instruction"))?
                    as usize;

                let return_address = self.program_counter.current_pos();
                self.stack.push(StackFrame::new(return_address));

                self.program_counter.go_to(call_address)?;
            }
            OpCode::Return => {
                let current_stack_frame = self
                    .stack
                    .pop()
                    .ok_or_else(|| anyhow!("Trying to return with an empty stack"))?;

                self.program_counter
                    .go_to(current_stack_frame.return_address)?;
            }
            OpCode::Exit => {
                let return_code = self.value_stack.pop()?;
                return Ok(VirtualMachineState::Exit(return_code as i64));
            }
            OpCode::Load => {
                let address = self
                    .value_stack
                    .pop()?
                    .try_into()
                    .map_err(|e: String| anyhow!(e))?;

                let value = match address {
                    Address::Stack(index, offset) => self.stack[index].locals[offset as usize],
                    Address::Heap(index) => (&self.heap[index..])
                        .read_u64::<BigEndian>()
                        .map_err(|e| anyhow!("Couldn't load word: {}", e))?,
                    Address::ROM(index) => (&self.rodata[index..])
                        .read_u64::<BigEndian>()
                        .map_err(|e| anyhow!("Couldn't load word: {}", e))?,
                };

                self.value_stack.push(value);
            }
            OpCode::Store => {
                let address = self
                    .value_stack
                    .pop()?
                    .try_into()
                    .map_err(|e: String| anyhow!(e))?;

                let value = self.value_stack.pop()?;

                match address {
                    Address::Stack(index, offset) => {
                        self.stack[index].locals[offset as usize] = value
                    }
                    Address::Heap(index) => (&mut self.heap[index..])
                        .write_u64::<BigEndian>(index as u64)
                        .map_err(|e| anyhow!("Couldn't store word: {}", e))?,
                    Address::ROM(index) => (&mut self.rodata[index..])
                        .write_u64::<BigEndian>(index as u64)
                        .map_err(|e| anyhow!("Couldn't store word: {}", e))?,
                }
            }
            OpCode::LoadByte => {
                let address = self
                    .value_stack
                    .pop()?
                    .try_into()
                    .map_err(|e: String| anyhow!(e))?;

                let value = match address {
                    Address::Stack(index, offset) => {
                        self.stack[index].locals[offset as usize] as u8
                    }
                    Address::Heap(index) => self.heap[index],
                    Address::ROM(index) => self.rodata[index],
                };

                self.value_stack.push(value as u64);
            }
            OpCode::StoreByte => {
                let address = self
                    .value_stack
                    .pop()?
                    .try_into()
                    .map_err(|e: String| anyhow!(e))?;

                let value = self.value_stack.pop()? as u8;

                match address {
                    Address::Stack(index, offset) => {
                        self.stack[index].locals[offset as usize] = value as u64
                    }
                    Address::Heap(index) => self.heap[index] = value,
                    Address::ROM(index) => self.rodata[index] = value,
                }
            }
            OpCode::StackAlloc => {
                let offset = {
                    let current_frame = self
                        .stack
                        .last_mut()
                        .ok_or_else(|| anyhow!("Trying to allocate on empty stack frame"))?;

                    if current_frame.locals.len() == u8::MAX as usize {
                        return Err(anyhow!("Tried to allocate more than 256 stack variables"));
                    }

                    current_frame.locals.push(0);
                    (current_frame.locals.len() - 1) as u8
                };

                let address = Address::Stack(self.stack.len() - 1, offset).into();
                self.value_stack.push(address);
            }
            OpCode::Print => {
                let raw_address = self.value_stack.pop()?;

                let address = raw_address.try_into().map_err(|e: String| anyhow!(e))?;
                let string_begin_ptr = match address {
                    Address::Heap(index) => unsafe { self.heap.as_ptr().add(index) },
                    Address::ROM(index) => unsafe { self.rodata.as_ptr().add(index) },
                    _ => return Err(anyhow!("Invalid string address: {:#x}", raw_address)),
                };

                let memory_end_ptr = match address {
                    Address::Heap(_) => unsafe { self.heap.as_ptr().add(self.heap.len()) },
                    Address::ROM(_) => unsafe { self.rodata.as_ptr().add(self.rodata.len()) },
                    _ => unreachable!(),
                };

                let mut cursor = string_begin_ptr;
                while unsafe { *cursor } != 0 {
                    cursor = unsafe { cursor.add(1) };
                    if cursor == memory_end_ptr {
                        return Err(anyhow!("Non null terminated string"));
                    }
                }

                let len = cursor as usize - string_begin_ptr as usize;

                let slice = unsafe { std::slice::from_raw_parts(string_begin_ptr, len) };
                let s = std::str::from_utf8(slice)
                    .map_err(|e| anyhow!("Invalid UTF-8 in string: {}", e))?;

                print!("{}", s);
            }
        }

        Ok(VirtualMachineState::Running)
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

        program.push(OpCode::Neg.into());

        let mut vm = VirtualMachine::new(program, vec![]);
        while let Ok(_) = vm.step() {}

        assert_eq!(vm.value_stack.pop().unwrap() as i64, -6);
    }

    #[test]
    fn jump() {
        let mut program = vec![];

        program.push(OpCode::Jump.into());
        12u64.to_be_bytes().iter().for_each(|b| program.push(*b));

        program.push(OpCode::Nop.into());
        program.push(OpCode::Nop.into());
        program.push(OpCode::Nop.into());

        let end = program.len();
        let mut vm = VirtualMachine::new(program, vec![]);
        vm.step().unwrap();

        assert_eq!(vm.program_counter.current_pos(), end);
    }
}
