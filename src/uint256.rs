pub use super::Int256;
use bnum::BUint;
use num_traits::{
    Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, FromPrimitive, Num, One, ToPrimitive,
    Zero,
};
use serde::ser::Serialize;
use serde::{Deserialize, Deserializer, Serializer};
use std::default::Default;
use std::fmt;
use std::num::IntErrorKind;
use std::ops::{
    Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Shl, ShlAssign, Shr,
    ShrAssign, Sub, SubAssign,
};
use std::str::FromStr;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Uint256(pub BUint<256>);

impl Uint256 {
    pub fn from_le_bytes(slice: &[u8]) -> Uint256 {
        // if the length is less than 32, pass that length
        // if it is greater truncate
        let end = if slice.len() <= 32 { slice.len() } else { 32 };
        Uint256(BUint::from_le_slice(&slice[0..end]).unwrap())
    }
    pub fn from_be_bytes(slice: &[u8]) -> Uint256 {
        // if the length is less than 32, pass that length
        // if it is greater truncate
        let end = if slice.len() <= 32 { slice.len() } else { 32 };
        Uint256(BUint::from_be_slice(&slice[0..end]).unwrap())
    }
    pub fn to_be_bytes(&self) -> [u8; 32] {
        let mut res = self.to_le_bytes();
        res.reverse();
        res
    }
    pub fn to_le_bytes(&self) -> [u8; 32] {
        let mut res: [u8; 32] = [0; 32];
        // the only function available to access the internal int representation is a bit by bit query
        // so in order to turn this into a 256bit array we must mask and shift this data into each byte
        for i in 0usize..256 {
            // the target byte and bit we are currently focused on
            let byte_index = i / 8;
            let bit_index = i % 8;
            // the bit we want to copy to the target
            let bit = self.0.bit(i as u32);
            // if true we mask a one with the byte at the right index
            if bit {
                let scratch_bit = 1u8 << bit_index;
                res[byte_index] |= scratch_bit
            }
        }
        res
    }
    /// Converts value to a signed 256 bit integer
    pub fn to_int256(&self) -> Option<Int256> {
        if *self <= Int256::max_value().to_uint256().unwrap() {
            Some(Int256::from_str_radix(&self.to_str_radix(10), 10).unwrap())
        } else {
            None
        }
    }

    /// Square root
    pub fn sqrt(&self) -> Uint256 {
        self.0.ilog(self.0).into()
    }
}

impl Num for Uint256 {
    type FromStrRadixErr = crate::error::ParseError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        let res = Uint256(BUint::<256>::from_str_radix(str, radix)?);
        if res > Uint256::max_value() {
            return Err(Self::FromStrRadixErr::new(IntErrorKind::PosOverflow));
        } else if res < Uint256::min_value() {
            return Err(Self::FromStrRadixErr::new(IntErrorKind::NegOverflow));
        }
        Ok(res)
    }
}

impl One for Uint256 {
    fn one() -> Self {
        Uint256(BUint::<256>::ONE)
    }
}

impl Zero for Uint256 {
    fn zero() -> Self {
        Uint256(BUint::<256>::ZERO)
    }

    fn is_zero(&self) -> bool {
        *self == Uint256::zero()
    }
}

impl FromPrimitive for Uint256 {
    fn from_i64(n: i64) -> Option<Self> {
        let val: Result<BUint<256>, _> = n.try_into();
        match val {
            Ok(v) => Some(Uint256(v)),
            Err(_) => None,
        }
    }

    fn from_u64(n: u64) -> Option<Self> {
        let val: BUint<256> = n.into();
        Some(Uint256(val))
    }
}

impl ToPrimitive for Uint256 {
    fn to_i64(&self) -> Option<i64> {
        match self.0.try_into() {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    }

    fn to_u64(&self) -> Option<u64> {
        match self.0.try_into() {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    }
}

impl Bounded for Uint256 {
    fn min_value() -> Self {
        // -2**255
        Uint256::zero()
    }
    fn max_value() -> Self {
        let max_value: Uint256 =
            "115792089237316195423570985008687907853269984665640564039457584007913129639935"
                .parse()
                .unwrap();
        max_value
    }
}

impl FromStr for Uint256 {
    type Err = crate::error::ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(val) = s.strip_prefix("0x") {
            Ok(BUint::<256>::from_str_radix(val, 16).map(Uint256)?)
        } else {
            Ok(BUint::<256>::from_str_radix(s, 10).map(Uint256)?)
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
        write!(f, "Uint256({})", &self.0.to_str_radix(10))
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
        write!(f, "{hex_str}")
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
        write!(f, "{hex_str}")
    }
}

impl Deref for Uint256 {
    type Target = BUint<256>;

    fn deref(&self) -> &BUint<256> {
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
        let (radix, data) = if let Some(val) = s.strip_prefix("0x") {
            (16, val)
        } else {
            (10, s.as_str())
        };

        // Create Uint256 given the sliced data, and radix
        BUint::<256>::from_str_radix(data, radix)
            .map(Uint256)
            .map_err(serde::de::Error::custom)
    }
}

impl From<[u8; 32]> for Uint256 {
    fn from(n: [u8; 32]) -> Uint256 {
        Uint256::from_be_bytes(&n)
    }
}

impl<'a> From<&'a [u8]> for Uint256 {
    fn from(n: &'a [u8]) -> Uint256 {
        Uint256::from_be_bytes(n)
    }
}

impl TryFrom<Int256> for Uint256 {
    type Error = ();

    fn try_from(value: Int256) -> Result<Self, Self::Error> {
        match value.to_uint256() {
            Some(v) => Ok(v),
            None => Err(()),
        }
    }
}

#[allow(clippy::from_over_into)]
impl Into<[u8; 32]> for Uint256 {
    fn into(self) -> [u8; 32] {
        self.to_be_bytes()
    }
}

macro_rules! uint_impl_from_uint {
    ($T:ty) => {
        impl From<$T> for Uint256 {
            #[inline]
            fn from(n: $T) -> Self {
                Uint256(BUint::<256>::from(n))
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
                let res = Uint256(res);
                // bounds check
                if res > Uint256::max_value() || res < Uint256::min_value() {
                    panic!("attempt to {} with overflow", stringify!($method));
                }
                res
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
                let value = a.$method(*b);
                match value {
                    Some(value) => {
                        let value = Uint256(value);
                        // bounds check
                        if value > Uint256::max_value() || value < Uint256::min_value() {
                            None
                        } else {
                            Some(value)
                        }
                    }
                    None => None,
                }
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
                // bounds check
                if *self > Uint256::max_value() || *self < Uint256::min_value() {
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

forward_op! { impl Shl for Uint256 { fn shl } }
forward_assign_op! { impl ShlAssign for Uint256 { fn shl_assign } }

forward_op! { impl Shr for Uint256 { fn shr } }
forward_assign_op! { impl ShrAssign for Uint256 { fn shr_assign } }

forward_op! { impl Rem for Uint256 { fn rem } }
forward_assign_op! { impl RemAssign for Uint256 { fn rem_assign } }

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
        format!("{lhs:#x}"),
        "0xbabababababababababababababababababababababababababababababababa"
    );
    assert_eq!(
        format!("{lhs:x}"),
        "babababababababababababababababababababababababababababababababa"
    );
    assert_eq!(
        format!("{lhs:X}"),
        "BABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABA"
    );
    assert_eq!(
        format!("{lhs:#X}"),
        "0xBABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABA"
    );
}

#[test]
fn to_hex_with_padding() {
    let lhs: Uint256 = "0xbababababababababababababababababababababababababababa"
        .parse()
        .unwrap();
    assert_eq!(
        format!("{lhs:#066x}"),
        "0x0000000000bababababababababababababababababababababababababababa"
    );
    assert_eq!(
        format!("{lhs:064x}"),
        "0000000000bababababababababababababababababababababababababababa"
    );
    assert_eq!(
        format!("{lhs:064X}"),
        "0000000000BABABABABABABABABABABABABABABABABABABABABABABABABABABA"
    );
    assert_eq!(
        format!("{lhs:#066X}"),
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
        format!("{val}"),
        "115792089237316195423570985008687907853269984665640564039457584007913129639935"
    );
    assert_eq!(
        val.to_string(),
        "115792089237316195423570985008687907853269984665640564039457584007913129639935"
    );
}

#[test]
fn check_from_str_radix_overflow() {
    let super_huge =
        "115792089237316195423570985008687907853369984665640564039457584007913129639935";
    let val = Uint256::from_str_radix(super_huge, 10);
    assert!(val.is_err())
}
