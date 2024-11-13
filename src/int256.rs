use bnum::types::I256;
use bnum::BInt;
use num_integer::Roots;
use num_traits::{
    Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, FromPrimitive, Num, One, Pow, Signed,
    ToPrimitive, Zero,
};
use serde::ser::Serialize;
use serde::{Deserialize, Deserializer, Serializer};
use std::fmt::{self};
use std::num::IntErrorKind;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::str::FromStr;

pub use crate::uint256::Uint256;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Int256(pub I256);

impl Int256 {
    pub fn from_le_bytes(slice: &[u8]) -> Int256 {
        // if the length is less than 32, pass that length
        // if it is greater truncate
        let end = if slice.len() <= 32 { slice.len() } else { 32 };
        Int256(BInt::from_le_slice(&slice[0..end]).unwrap())
    }
    pub fn from_be_bytes(slice: &[u8]) -> Int256 {
        // if the length is less than 32, pass that length
        // if it is greater truncate
        let end = if slice.len() <= 32 { slice.len() } else { 32 };
        Int256(BInt::from_be_slice(&slice[0..end]).unwrap())
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

    /// Square root
    pub fn sqrt(&self) -> Uint256 {
        Uint256(self.0.sqrt().unsigned_abs())
    }

    /// Checked conversion to Uint256
    pub fn to_uint256(&self) -> Option<Uint256> {
        if *self < Int256::zero() {
            None
        } else {
            Some(Uint256(self.0.unsigned_abs()))
        }
    }

    pub fn to_str_radix(&self, rdx: u32) -> String {
        self.0.to_str_radix(rdx)
    }
}

impl Num for Int256 {
    type FromStrRadixErr = crate::error::ParseError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        let res = Int256(I256::from_str_radix(str, radix)?);
        if res > Int256::max_value() {
            return Err(Self::FromStrRadixErr::new(IntErrorKind::PosOverflow));
        } else if res < Int256::min_value() {
            return Err(Self::FromStrRadixErr::new(IntErrorKind::NegOverflow));
        }
        Ok(res)
    }
}

impl One for Int256 {
    fn one() -> Self {
        Int256(I256::ONE)
    }
}

impl Zero for Int256 {
    fn zero() -> Self {
        Int256(I256::ZERO)
    }

    fn is_zero(&self) -> bool {
        *self == Int256::zero()
    }
}

impl FromPrimitive for Int256 {
    fn from_i64(n: i64) -> Option<Self> {
        let val: I256 = n.into();
        Some(Int256(val))
    }

    fn from_u64(n: u64) -> Option<Self> {
        let val: I256 = n.into();
        Some(Int256(val))
    }

    fn from_i128(n: i128) -> Option<Self> {
        let val: I256 = n.into();
        Some(Int256(val))
    }

    fn from_u128(n: u128) -> Option<Self> {
        let val: I256 = n.into();
        Some(Int256(val))
    }
}

impl ToPrimitive for Int256 {
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

    fn to_i128(&self) -> Option<i128> {
        match self.0.try_into() {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    }

    fn to_u128(&self) -> Option<u128> {
        match self.0.try_into() {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    }
}

impl Neg for Int256 {
    type Output = Int256;

    fn neg(self) -> Self::Output {
        Int256(self.0.neg())
    }
}

impl Bounded for Int256 {
    fn min_value() -> Self {
        let min_value: Int256 =
            "-57896044618658097711785492504343953926634992332820282019728792003956564819968"
                .parse()
                .unwrap();
        min_value
    }
    fn max_value() -> Self {
        let min_value: Int256 =
            "57896044618658097711785492504343953926634992332820282019728792003956564819967"
                .parse()
                .unwrap();
        min_value
    }
}

macro_rules! impl_from_int {
    ($T:ty) => {
        impl From<$T> for Int256 {
            #[inline]
            fn from(n: $T) -> Self {
                Int256(I256::from(n))
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
        *n
    }
}

impl FromStr for Int256 {
    type Err = crate::error::ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Int256(I256::from_str_radix(s, 10)?))
    }
}

impl TryFrom<&str> for Int256 {
    type Error = crate::error::ParseError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        value.parse()
    }
}

impl TryFrom<Uint256> for Int256 {
    type Error = ();

    fn try_from(value: Uint256) -> Result<Self, Self::Error> {
        match value.to_int256() {
            Some(v) => Ok(v),
            None => Err(()),
        }
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

        I256::from_str(&s)
            .map(Int256)
            .map_err(serde::de::Error::custom)
    }
}

impl Signed for Int256 {
    fn abs(&self) -> Self {
        Int256(self.0.abs())
    }
    fn abs_sub(&self, other: &Self) -> Self {
        if self <= other {
            Int256::zero()
        } else {
            *self - *other
        }
    }
    fn signum(&self) -> Self {
        Int256(self.0.signum())
    }
    fn is_positive(&self) -> bool {
        self.0.is_positive()
    }
    fn is_negative(&self) -> bool {
        self.0.is_negative()
    }
}

impl Pow<u32> for Int256 {
    type Output = Self;

    fn pow(self, p: u32) -> Self::Output {
        Int256(self.0.pow(p))
    }
}

/// A macro that forwards an unary operator trait i.e. Add
macro_rules! forward_op {
    (impl $trait_: ident for $type_: ident { fn $method: ident }) => {
        impl $trait_<$type_> for $type_ {
            type Output = $type_;

            fn $method(self, $type_(b): $type_) -> $type_ {
                let $type_(a) = self;
                $type_(a.$method(&b))
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
                let value = a.$method(b);
                match value {
                    Some(value) => Some(Int256(value)),
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
                // Borrow happens only inside this scope
                {
                    let a = &mut self.0;
                    a.$method(b);
                }
            }
        }
    };
}

forward_op! { impl Add for Int256 { fn add } }
forward_checked_op! { impl CheckedAdd for Int256 { fn checked_add } }
forward_assign_op! { impl AddAssign for Int256 { fn add_assign } }

forward_op! { impl Sub for Int256 { fn sub } }
forward_checked_op! { impl CheckedSub for Int256 { fn checked_sub } }
forward_assign_op! { impl SubAssign for Int256 { fn sub_assign } }

forward_op! { impl Mul for Int256 { fn mul } }
forward_checked_op! { impl CheckedMul for Int256 { fn checked_mul } }
forward_assign_op! { impl MulAssign for Int256 { fn mul_assign } }

forward_op! { impl Div for Int256 { fn div } }
forward_checked_op! { impl CheckedDiv for Int256 { fn checked_div } }
forward_assign_op! { impl DivAssign for Int256 { fn div_assign } }

forward_op! { impl Rem for Int256 { fn rem } }
forward_assign_op! { impl RemAssign for Int256 { fn rem_assign } }

#[test]
fn check_from_str_radix_overflow_underflow() {
    let super_huge =
        "115792089237316195423570985008687907853369984665640564039457584007913129639935";
    let super_small =
        "-67896044618658097711785492504343953926634992332820282019728792003956564819968";
    let val = Int256::from_str_radix(super_huge, 10);
    assert!(val.is_err());
    let val = Int256::from_str_radix(super_small, 10);
    assert!(val.is_err());
}

/// Check the ToPrimitive impl for +-[0, 100k] and +-[2^32-100, ~2^32+100k]
#[test]
fn test_to_primitive_64() {
    use num_traits::ToPrimitive;
    let u32_max: u64 = u32::MAX.into();
    let mut i = 0u64;
    while i < 100_000 {
        let i_int256: Int256 = i.into();
        assert_eq!(i, (i_int256).to_u64().unwrap());
        assert_eq!(i as i64, (i_int256).to_i64().unwrap());
        let neg_int256: Int256 = i_int256.neg();
        assert_eq!(-(i as i64), (neg_int256).to_i64().unwrap());
        i += 1
    }

    let mut i: u64 = u32_max - 100;
    let end = i + 100_000;
    while i < end {
        let i_int256: Int256 = i.into();
        assert_eq!(i, i_int256.to_u64().unwrap());
        if i < u32_max {
            assert_eq!(i as i64, i_int256.to_i64().unwrap());
            let neg_int256: Int256 = i_int256.neg();
            assert_eq!(-(i as i64), neg_int256.to_i64().unwrap());
        }

        i += 1
    }
}

/// Check the ToPrimitive impl for +-[0, 100k] and +-[2^64-100, ~2^64+100k]
#[test]
fn test_to_primitive_128() {
    let u64_max: u128 = u64::MAX.into();
    use num_traits::ToPrimitive;
    let mut i = 0u128;
    while i < 100_000 {
        let i_int256: Int256 = i.into();
        assert_eq!(i, i_int256.to_u128().unwrap());
        assert_eq!(i as i128, i_int256.to_i128().unwrap());
        let neg_int256: Int256 = i_int256.neg();
        assert_eq!(-(i as i128), (neg_int256).to_i128().unwrap());
        i += 1
    }
    let mut i: u128 = u64_max - 100;
    let end = i + 100_000;
    while i < end {
        let i_int256: Int256 = i.into();
        assert_eq!(i, i_int256.to_u128().unwrap());
        if i < u64_max {
            assert_eq!(i as i128, i_int256.to_i128().unwrap());
            let neg_int256: Int256 = i_int256.neg();
            assert_eq!(-(i as i128), neg_int256.to_i128().unwrap());
        }
        i += 1
    }
}

/// Check the implementations of to_be_bytes, to_le_bytes, from_be_bytes, from_le_bytes
#[test]
fn test_to_from_bytes() {
    let to_from_be = |n: Int256| Int256::from_be_bytes(&n.to_be_bytes());
    let to_from_le = |n: Int256| Int256::from_le_bytes(&n.to_le_bytes());

    let n1 = Int256::from(-1i8);
    let z = Int256::zero();
    let p1 = Int256::from(1i8);
    let p_u64max = Int256::from(u64::MAX);
    let n_u64max = p_u64max.neg();
    let p_u128max = Int256::from(u128::MAX);
    let n_u128max = p_u128max.neg();
    let int256_max = Int256::max_value();
    let int256_min = Int256::min_value();
    let test_cases = vec![
        n1, z, p1, p_u64max, n_u64max, p_u128max, n_u128max, int256_max, int256_min,
    ];

    for tc in test_cases {
        assert_eq!(tc, to_from_be(tc));
        assert_eq!(tc, to_from_le(tc));
    }
}

#[test]
fn test_sqrt() {
    use rand::prelude::*;

    for _ in 1..100000 {
        let r: i128 = random();
        let n = Int256::from(r.abs());
        let sqrt = (n.mul(n)).sqrt();
        assert!(sqrt == n.to_uint256().unwrap());
    }
}
