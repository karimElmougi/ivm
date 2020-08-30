use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::io::{self, Read};

use anyhow::{anyhow, Result};
use num_traits::PrimInt;

const SHIFT_SIZE: usize = size_in_bits::<u64>() - 2;
pub const ROM_ADDRESS_MASK: usize = 0b10 << SHIFT_SIZE;
const HEAP_ADDRESS_MASK: usize = 0b01 << SHIFT_SIZE;

#[derive(Default)]
pub struct Allocation {
    pub size: usize,
    pub is_managed: bool,
}

#[derive(Default)]
pub struct ValueStack(Vec<u64>);

impl ValueStack {
    pub fn push(&mut self, value: u64) {
        self.0.push(value);
    }

    pub fn pop(&mut self) -> Result<u64> {
        self.0.pop().ok_or_else(|| anyhow!("Value stack is empty"))
    }

    pub fn pop_2(&mut self) -> Result<(u64, u64)> {
        self.0
            .pop()
            .and_then(|op2| self.0.pop().map(|op1| (op1, op2)))
            .ok_or_else(|| anyhow!("Value stack is empty"))
    }
}

pub struct StackFrame {
    pub return_address: usize,
    pub locals: Vec<u64>,
}

impl StackFrame {
    pub fn new(return_address: usize) -> Self {
        Self {
            return_address,
            locals: Default::default(),
        }
    }
}

pub enum Address {
    Stack(usize, u8),
    Heap(usize),
    ROM(usize),
}

impl TryFrom<u64> for Address {
    type Error = String;

    fn try_from(value: u64) -> std::result::Result<Address, Self::Error> {
        let mask = 0b11u64 << SHIFT_SIZE;
        let index = (value & !mask) as usize;

        let address = match (value & mask) >> SHIFT_SIZE {
            0b00 => {
                let offset_mask = u8::MAX as usize;
                let stack_frame_index = (index & !offset_mask) >> size_in_bits::<u8>();
                let local_variable_index = (index & offset_mask) as u8;
                Address::Stack(stack_frame_index, local_variable_index)
            }
            0b01 => Address::Heap(index),
            0b10 => Address::ROM(index),
            _ => return Err(format!("Invalid address: {:#x}", value)),
        };

        Ok(address)
    }
}

impl Into<u64> for Address {
    fn into(self) -> u64 {
        (match self {
            Address::Stack(index, offset) => index << size_in_bits::<u8>() | offset as usize,
            Address::Heap(index) => HEAP_ADDRESS_MASK | index,
            Address::ROM(index) => ROM_ADDRESS_MASK | index,
        }) as u64
    }
}

pub struct Cursor<I>
where
    I: PrimInt,
{
    #[allow(dead_code)]
    program: Immutable<Vec<I>>,
    begin: *const I,
    end: *const I,
    cursor: *const I,
}

impl<I> Cursor<I>
where
    I: PrimInt,
{
    pub fn new(program: Vec<I>) -> Self {
        let begin = program.as_ptr();
        let end = unsafe { begin.add(program.len()) };
        Self {
            program: Immutable::new(program),
            begin,
            end,
            cursor: begin,
        }
    }

    pub fn next(&mut self) -> Option<I> {
        if self.cursor != self.end {
            let value = unsafe { *self.cursor };
            self.cursor = unsafe { self.cursor.add(1) };
            Some(value)
        } else {
            None
        }
    }

    pub fn go_to(&mut self, pos: usize) -> Result<()> {
        let new_cursor = unsafe { self.begin.add(pos) };
        if new_cursor <= self.end {
            self.cursor = new_cursor;
            Ok(())
        } else {
            Err(anyhow!("Position out of bounds"))
        }
    }

    pub fn current_pos(&self) -> usize {
        self.cursor as usize - self.begin as usize
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

    #[allow(dead_code)]
    fn as_ref(&self) -> &T {
        &self.0
    }
}

pub const fn size_in_bits<T>() -> usize {
    std::mem::size_of::<T>() * 8
}

pub trait FindUnusedChunk {
    fn find_unused_chunk(&self, size: usize, heap_end: usize) -> Option<usize>;
}

impl FindUnusedChunk for BTreeMap<usize, Allocation> {
    fn find_unused_chunk(&self, size: usize, heap_end: usize) -> Option<usize> {
        let mut iter = self.iter().peekable();
        while let Some((index, allocation)) = iter.next() {
            let next_index = iter
                .peek()
                .and_then(|p| Some(*p.0))
                .or(Some(heap_end))
                .unwrap();

            let free_gap = next_index - (index + allocation.size);

            if size as usize <= free_gap {
                return Some(index + allocation.size);
            }
        }

        None
    }
}
