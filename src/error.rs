use core::fmt::{self, Debug, Display, Formatter};
use std::num::IntErrorKind;

#[derive(PartialEq, Eq, Clone)]
pub struct ParseError {
    pub kind: IntErrorKind,
}

impl ParseError {
    pub const fn kind(&self) -> &IntErrorKind {
        &self.kind
    }

    const fn description(&self) -> &str {
        match &self.kind {
            IntErrorKind::Empty => "attempt to parse integer from empty string",
            IntErrorKind::InvalidDigit => {
                "attempt to parse integer from string containing invalid digit"
            }
            IntErrorKind::PosOverflow => {
                "attempt to parse integer too large to be represented by the target type"
            }
            IntErrorKind::NegOverflow => {
                "attempt to parse integer too small to be represented by the target type"
            }
            IntErrorKind::Zero => {
                "attempt to parse the integer `0` which cannot be represented by the target type"
            }
            _ => panic!("unsupported `IntErrorKind` variant"), // necessary as `IntErrorKind` is non-exhaustive
        }
    }
}

impl ParseError {
    pub fn new(kind: IntErrorKind) -> ParseError {
        ParseError { kind }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "(num256) {}", self.description())
    }
}

impl Debug for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(&self, f)
    }
}

impl From<bnum::errors::ParseIntError> for ParseError {
    fn from(value: bnum::errors::ParseIntError) -> Self {
        ParseError {
            kind: value.kind().clone(),
        }
    }
}
