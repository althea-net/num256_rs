pub use super::Int256;
use failure::Error;
use num::bigint::ParseBigIntError;
use num::bigint::ToBigInt;
use num::traits::ops::checked::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};
use num::BigUint;
use num::Num;
use num::{pow, Bounded, Zero};
use serde;
use serde::ser::Serialize;
use serde::{Deserialize, Deserializer, Serializer};
use std::default::Default;
use std::fmt;
use std::ops::{Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, FromPrimitive, ToPrimitive, Zero, Default)]
pub struct Uint256(pub BigUint);

impl Uint256 {
    pub fn from_bytes_le(slice: &[u8]) -> Uint256 {
        Uint256(BigUint::from_bytes_le(slice))
    }
    pub fn from_bytes_be(slice: &[u8]) -> Uint256 {
        Uint256(BigUint::from_bytes_be(slice))
    }
    pub fn from_str_radix(s: &str, radix: u32) -> Result<Uint256, ParseBigIntError> {
        BigUint::from_str_radix(s, radix).map(Uint256)
    }
    /// Converts value to a signed 256 bit integer
    pub fn to_int256(&self) -> Option<Int256> {
        self.0
            .to_bigint()
            .filter(|value| value.bits() <= 255)
            .map(Int256)
    }
}

impl Bounded for Uint256 {
    fn min_value() -> Self {
        // -2**255
        Uint256::zero()
    }
    fn max_value() -> Self {
        lazy_static! {
            static ref MAX_VALUE: BigUint = pow(BigUint::from(2u32), 256) - BigUint::from(1u32);
        }
        Uint256(MAX_VALUE.clone())
    }
}

impl FromStr for Uint256 {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("0x") {
            Ok(BigUint::from_str_radix(&s[2..], 16).map(Uint256)?)
        } else {
            Ok(BigUint::from_str_radix(&s, 10).map(Uint256)?)
        }
    }
}

impl fmt::Display for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.0.to_str_radix(10))
    }
}

impl fmt::Debug for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Uint256({})", self.to_string())
    }
}

impl fmt::LowerHex for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let hex_str = &self.0.to_str_radix(16);
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
        let hex_str = &self.0.to_str_radix(16).to_uppercase();
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

impl Deref for Uint256 {
    type Target = BigUint;

    fn deref(&self) -> &BigUint {
        &self.0
    }
}

impl Serialize for Uint256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.0.to_str_radix(10))
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
        let (radix, data) = if s.starts_with("0x") {
            (16, &s[2..])
        } else {
            (10, s.as_str())
        };

        // Create Uint256 given the sliced data, and radix
        BigUint::from_str_radix(data, radix)
            .map(Uint256)
            .map_err(serde::de::Error::custom)
    }
}

impl From<[u8; 32]> for Uint256 {
    fn from(n: [u8; 32]) -> Uint256 {
        Uint256(BigUint::from_bytes_be(&n))
    }
}

impl<'a> From<&'a [u8]> for Uint256 {
    fn from(n: &'a [u8]) -> Uint256 {
        Uint256(BigUint::from_bytes_be(n))
    }
}

impl Into<[u8; 32]> for Uint256 {
    fn into(self) -> [u8; 32] {
        let bytes = self.0.to_bytes_be();
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
                Uint256(BigUint::from(n))
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

/// A macro that forwards an unary operator trait i.e. Add
macro_rules! forward_op {
    (impl $trait_: ident for $type_: ident { fn $method: ident }) => {
        impl $trait_<$type_> for $type_ {
            type Output = $type_;

            fn $method(self, $type_(b): $type_) -> $type_ {
                let $type_(a) = self;
                let res = a.$method(&b);
                if res.bits() > 256 {
                    panic!("attempt to {} with overflow", stringify!($method));
                }
                $type_(res)
            }
        }
    };
}

/// A macro that forwards a checked operator i.e. CheckedAdd
macro_rules! forward_checked_op {
    (impl $trait_: ident for $type_: ident { fn $method: ident }) => {
        impl $trait_ for $type_ {
            fn $method(&self, $type_(b): &$type_) -> Option<$type_> {
                let $type_(a) = self;
                a.$method(&b)
                    .filter(|value| value.bits() <= 256)
                    .map($type_)
            }
        }
    };
}

/// A macro that forwards a assignment operator i.e. AddAssign
macro_rules! forward_assign_op {
    (impl $trait_: ident for $type_: ident { fn $method: ident }) => {
        impl $trait_ for $type_ {
            fn $method(&mut self, $type_(b): $type_) {
                let a = &mut self.0;
                a.$method(b);
                if a.bits() > 256 {
                    panic!("attempt to {} with overflow", stringify!($method));
                }
            }
        }
    };
}

forward_op! { impl Add for Uint256 { fn add } }
forward_checked_op! { impl CheckedAdd for Uint256 { fn checked_add } }
forward_assign_op! { impl AddAssign for Uint256 { fn add_assign } }

forward_op! { impl Sub for Uint256 { fn sub } }
forward_checked_op! { impl CheckedSub for Uint256 { fn checked_sub } }
forward_assign_op! { impl SubAssign for Uint256 { fn sub_assign } }

forward_op! { impl Mul for Uint256 { fn mul } }
forward_checked_op! { impl CheckedMul for Uint256 { fn checked_mul } }
forward_assign_op! { impl MulAssign for Uint256 { fn mul_assign } }

forward_op! { impl Div for Uint256 { fn div } }
forward_checked_op! { impl CheckedDiv for Uint256 { fn checked_div } }
forward_assign_op! { impl DivAssign for Uint256 { fn div_assign } }

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
