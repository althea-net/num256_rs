pub use crate::uint256::Uint256;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use std::num::{IntErrorKind, ParseIntError};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Int256 {
    /// true if negative
    sign: bool,
    /// least significant bits (little endian)
    upper: u128,
    /// most significant bits (little endian)
    lower: u128,
}

impl Int256 {
    /// Checked conversion to Uint256
    pub fn to_uint256(&self) -> Option<Uint256> {
        if self.sign {
            None
        } else {
            Some(Uint256 {
                upper: self.upper,
                lower: self.lower,
            })
        }
    }

    pub const fn min_value() -> Int256 {
        Int256::MIN
    }

    pub const MIN: Int256 = Int256 {
        sign: true,
        upper: u128::MAX,
        lower: u128::MAX,
    };

    pub const fn max_value() -> Int256 {
        Int256::MAX
    }

    pub const MAX: Int256 = Int256 {
        sign: false,
        upper: u128::MAX,
        lower: u128::MAX,
    };

    pub fn from_str_radix(src: &str, radix: u32) -> Result<Uint256, ParseIntError> {
        use std::num::IntErrorKind::*;
        use std::num::ParseIntError as PIE;

        assert!(
            radix >= 2 && radix <= 36,
            "from_str_radix_int: must lie in the range `[2, 36]` - found {}",
            radix
        );

        if src.is_empty() {
            return Err(PIE { kind: Empty });
        }

        let is_signed_ty = Int256::from_u32(0) > Int256::min_value();

        // all valid digits are ascii, so we will just iterate over the utf8 bytes
        // and cast them to chars. .to_digit() will safely return None for anything
        // other than a valid ascii digit for the given radix, including the first-byte
        // of multi-byte sequences
        let src = src.as_bytes();

        let (is_positive, digits) = match src[0] {
            b'+' => (true, &src[1..]),
            b'-' if is_signed_ty => (false, &src[1..]),
            _ => (true, src),
        };

        if digits.is_empty() {
            return Err(PIE { kind: Empty });
        }

        let mut result = Int256::from_u32(0);
        if is_positive {
            // The number is positive
            for &c in digits {
                let x = match (c as char).to_digit(radix) {
                    Some(x) => x,
                    None => return Err(PIE { kind: InvalidDigit }),
                };
                result = match result.checked_mul(radix) {
                    Some(result) => result,
                    None => {
                        return Err(PIE {
                            kind: IntErrorKind::PosOverflow,
                        })
                    }
                };
                result = match result.checked_add(x) {
                    Some(result) => result,
                    None => {
                        return Err(PIE {
                            kind: IntErrorKind::PosOverflow,
                        })
                    }
                };
            }
        } else {
            // The number is negative
            for &c in digits {
                let x = match (c as char).to_digit(radix) {
                    Some(x) => x,
                    None => return Err(PIE { kind: InvalidDigit }),
                };
                result = match result.checked_mul(radix) {
                    Some(result) => result,
                    None => {
                        return Err(PIE {
                            kind: IntErrorKind::NegOverflow,
                        })
                    }
                };
                result = match result.checked_sub(x) {
                    Some(result) => result,
                    None => {
                        return Err(PIE {
                            kind: IntErrorKind::NegOverflow,
                        })
                    }
                };
            }
        }

        Ok(result)
    }
}

macro_rules! impl_from_int {
    ($T:ty) => {
        impl From<$T> for Int256 {
            #[inline]
            fn from(n: $T) -> Self {
                Int256::from(n)
            }
        }
    };
}

impl_from_int!(i8);
impl_from_int!(i16);
impl_from_int!(i32);
impl_from_int!(i64);
impl_from_int!(i128);
impl_from_int!(isize);
impl_from_int!(u8);
impl_from_int!(u16);
impl_from_int!(u32);
impl_from_int!(u64);
impl_from_int!(u128);
impl_from_int!(usize);

impl<'a> From<&'a Int256> for Int256 {
    fn from(n: &Int256) -> Int256 {
        n.clone()
    }
}

impl fmt::Display for Int256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.to_str_radix(10))
    }
}

impl fmt::Debug for Int256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Int256({})", &self.0.to_str_radix(10))
    }
}

impl Serialize for Int256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_str_radix(10))
    }
}

impl<'de> Deserialize<'de> for Int256 {
    fn deserialize<D>(deserializer: D) -> Result<Int256, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Int256::from_str_radix(&s, 10)
    }
}

impl Add for Int256 {}

impl Sub for Int256 {}

impl Mul for Int256 {}

impl Div for Int256 {}

impl AddAssign for Int256 {}

impl SubAssign for Int256 {}

impl MulAssign for Int256 {}

impl DivAssign for Int256 {}

impl RemAssign for Int256 {}

impl Neg for Int256 {}
