pub use super::Int256;
use serde::de::Error as SerdeError;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::default::Default;
use std::fmt;
use std::num::{IntErrorKind, ParseIntError};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Uint256 {
    /// lower bits, little endian internal representation
    upper: u128,
    lower: u128,
}

impl Uint256 {
    pub const fn min_value() -> Uint256 {
        Uint256::MIN
    }

    pub const MIN: Uint256 = Uint256 {
        upper: u128::MAX,
        lower: u128::MAX,
    };

    pub const fn max_value() -> Uint256 {
        Uint256::MAX
    }

    pub const MAX: Uint256 = Uint256 {
        upper: u128::MAX,
        lower: u128::MAX,
    };

    /// Converts value to a signed 256 bit integer
    pub fn to_int256(&self) -> Option<Int256> {
        if *self > Int256::MAX.to_uint256().unwrap() {
            return None;
        } else {
            Some(Int256 {
                sign: false,
                upper: self.upper,
                lower: self.lower,
            })
        }
    }

    pub fn from_le_bytes(slice: [u8; 32]) -> Uint256 {
        let mut upper: [u8; 16];
        let mut lower: [u8; 16];
        upper.copy_from_slice(&slice[16..32]);
        lower.copy_from_slice(&slice[0..16]);
        Uint256 {
            upper: u128::from_le_bytes(upper),
            lower: u128::from_le_bytes(lower),
        }
    }
    pub fn to_le_bytes(&self) -> [u8; 32] {
        let mut res = [0; 32];
        let bytes = self.lower.to_le_bytes().to_vec();
        bytes.extend(self.lower.to_le_bytes());
        res.clone_from_slice(&bytes[0..32]);
        res
    }
    pub fn from_be_bytes(slice: [u8; 32]) -> Uint256 {
        let mut upper: [u8; 16];
        let mut lower: [u8; 16];
        upper.copy_from_slice(&slice[0..16]);
        lower.copy_from_slice(&slice[16..32]);
        Uint256 {
            upper: u128::from_be_bytes(upper),
            lower: u128::from_be_bytes(lower),
        }
    }
    pub fn to_be_bytes(&self) -> [u8; 32] {
        let mut res = [0; 32];
        let bytes = self.upper.to_be_bytes().to_vec();
        bytes.extend(self.lower.to_be_bytes());
        res.clone_from_slice(&bytes[0..32]);
        res
    }
    fn to_str_radix(&self, radix: u32) -> String {
        assert!(
            radix >= 2 && radix <= 36,
            "to_str_radix_int: must lie in the range `[2, 36]` - found {}",
            radix
        );
    }
    fn from_str_radix(src: &str, radix: u32) -> Result<Uint256, ParseIntError> {
        use self::ParseIntError as PIE;
        use std::num::IntErrorKind::*;

        assert!(
            radix >= 2 && radix <= 36,
            "from_str_radix_int: must lie in the range `[2, 36]` - found {}",
            radix
        );

        if src.is_empty() {
            return Err(PIE { kind: Empty });
        }

        let is_signed_ty = Uint256::from_u32(0) > Uint256::min_value();

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

        let mut result = Uint256::from_u32(0);
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
            return Err(PIE {
                kind: IntErrorKind::InvalidDigit,
            });
        }
        Ok(result)
    }
}

impl FromStr for Uint256 {
    type Err = ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(val) = s.strip_prefix("0x") {
            Uint256::from_str_radix(val, 16)
        } else {
            Uint256::from_str_radix(s, 10)
        }
    }
}

impl fmt::Display for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.to_str_radix(10))
    }
}

impl fmt::Debug for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Uint256({})", &self.to_str_radix(10))
    }
}

impl fmt::LowerHex for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let hex_str = &self.to_str_radix(16);
        let mut width = hex_str.len();
        if f.alternate() {
            write!(f, "0x")?;
            width += 2;
        }
        if let Some(desired_width) = f.width() {
            if desired_width > width {
                let pad = String::from_utf8(vec![b'0'; desired_width - width]).unwrap();
                write!(f, "{}", &pad)?;
            }
        }
        write!(f, "{}", hex_str)
    }
}

impl fmt::UpperHex for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let hex_str = &self.to_str_radix(16).to_uppercase();
        let mut width = hex_str.len();
        if f.alternate() {
            write!(f, "0x")?;
            width += 2;
        }
        if let Some(desired_width) = f.width() {
            if desired_width > width {
                let pad = String::from_utf8(vec![b'0'; desired_width - width]).unwrap();
                write!(f, "{}", &pad)?;
            }
        }
        write!(f, "{}", hex_str)
    }
}

impl Serialize for Uint256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_str_radix(10))
    }
}

impl<'de> Deserialize<'de> for Uint256 {
    fn deserialize<D>(deserializer: D) -> Result<Uint256, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;

        // Decide how to deserialize 256 bit integer based on the representation.
        // "0x" prefix means the string contains hexadecmial representation of the number,
        // lack of it means its decimal.
        let (radix, data) = if let Some(val) = s.strip_prefix("0x") {
            (16, val)
        } else {
            (10, s.as_str())
        };

        // Create Uint256 given the sliced data, and radix
        match Uint256::from_str_radix(data, radix) {
            Ok(v) => Ok(v),
            Err(e) => Err(SerdeError::custom(e.to_string())),
        }
    }
}

impl From<[u8; 32]> for Uint256 {
    fn from(n: [u8; 32]) -> Uint256 {
        Uint256::from_le_bytes(n)
    }
}

impl<'a> From<&'a [u8]> for Uint256 {
    fn from(n: &'a [u8]) -> Uint256 {
        let mut bytes: [u8; 32];
        // if a value larger than 32 bytes is provided, take
        // the first 32 bytes
        let mut count = 0;
        for i in n.iter() {
            if count > 31 {
                break;
            }
            bytes[count] = *i;
        }
        Uint256::from_be_bytes(bytes)
    }
}

#[allow(clippy::from_over_into)]
impl Into<[u8; 32]> for Uint256 {
    fn into(self) -> [u8; 32] {
        let bytes = self.to_be_bytes();
        let mut res: [u8; 32] = Default::default();
        res[32 - bytes.len()..].copy_from_slice(&bytes);
        res
    }
}

macro_rules! uint_impl_from_uint {
    ($T:ty) => {
        impl From<$T> for Uint256 {
            #[inline]
            fn from(n: $T) -> Self {
                Uint256::from(n)
            }
        }
    };
}

// These implementations are pretty much guaranteed to be panic-free.
uint_impl_from_uint!(u8);
uint_impl_from_uint!(u16);
uint_impl_from_uint!(u32);
uint_impl_from_uint!(u64);
uint_impl_from_uint!(u128);
uint_impl_from_uint!(usize);

impl Add for Uint256 {}

impl Sub for Uint256 {}

impl Mul for Uint256 {}

impl Div for Uint256 {}

impl AddAssign for Uint256 {}

impl SubAssign for Uint256 {}

impl MulAssign for Uint256 {}

impl DivAssign for Uint256 {}

#[test]
fn create_from_32_bytes() {
    let lhs: [u8; 32] = [
        0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42,
        0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42,
        0x42, 0x42,
    ];
    let lhs: Uint256 = lhs.into();
    assert_eq!(
        lhs,
        "0x4242424242424242424242424242424242424242424242424242424242424242"
            .parse()
            .unwrap()
    );
}

#[test]
fn to_hex() {
    let lhs: Uint256 = "0xbabababababababababababababababababababababababababababababababa"
        .parse()
        .unwrap();
    assert_eq!(
        format!("{:#x}", lhs),
        "0xbabababababababababababababababababababababababababababababababa"
    );
    assert_eq!(
        format!("{:x}", lhs),
        "babababababababababababababababababababababababababababababababa"
    );
    assert_eq!(
        format!("{:X}", lhs),
        "BABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABA"
    );
    assert_eq!(
        format!("{:#X}", lhs),
        "0xBABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABA"
    );
}

#[test]
fn to_hex_with_padding() {
    let lhs: Uint256 = "0xbababababababababababababababababababababababababababa"
        .parse()
        .unwrap();
    assert_eq!(
        format!("{:#066x}", lhs),
        "0x0000000000bababababababababababababababababababababababababababa"
    );
    assert_eq!(
        format!("{:064x}", lhs),
        "0000000000bababababababababababababababababababababababababababa"
    );
    assert_eq!(
        format!("{:064X}", lhs),
        "0000000000BABABABABABABABABABABABABABABABABABABABABABABABABABABA"
    );
    assert_eq!(
        format!("{:#066X}", lhs),
        "0x0000000000BABABABABABABABABABABABABABABABABABABABABABABABABABABA"
    );
}

#[test]
fn into_array() {
    let val = Uint256::from(1024u16);
    let data: [u8; 32] = val.into();
    assert_eq!(
        data,
        [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 4, 0
        ]
    );
}

#[test]
fn check_display() {
    let val = Uint256::max_value();
    assert_eq!(
        format!("{}", val),
        "115792089237316195423570985008687907853269984665640564039457584007913129639935"
    );
    assert_eq!(
        val.to_string(),
        "115792089237316195423570985008687907853269984665640564039457584007913129639935"
    );
}
