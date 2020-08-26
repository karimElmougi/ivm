use std::fmt::{self, Display};

use num_enum::{IntoPrimitive, TryFromPrimitive};

#[derive(TryFromPrimitive, IntoPrimitive, Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum OpCode {
    Nop,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Neg,
    Inc,
    Dec,
    Equal,
    NotEqual,
    GreaterThanOrEqual,
    LessThanOrEqual,
    GreaterThan,
    LessThan,
    Push,
    PushStackPointer,
    Load,
    Store,
    LoadByte,
    StoreByte,
    StackAlloc,
    Jump,
    ConditionalJump,
    Print,
    Call,
    Return,
    Exit,
}

impl Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
