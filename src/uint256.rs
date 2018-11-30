pub use super::Int256;
use failure::Error;
use num::bigint::ParseBigIntError;
use num::traits::ops::checked::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};
use num::{BigInt, BigUint};
use num::{Num, Zero};
use serde;
use serde::ser::Serialize;
use serde::{Deserialize, Deserializer, Serializer};
use std::fmt;
use std::ops::{Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
}

impl Zero for Uint256 {
    fn zero() -> Uint256 {
        Uint256(BigUint::zero())
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
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
        write!(f, "{:x}", &self.0)
    }
}

impl fmt::Debug for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Uint256({})", self.to_string())
    }
}

impl fmt::LowerHex for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.alternate() {
            write!(f, "0x")?;
        }
        write!(f, "{}", self.0.to_str_radix(16))
    }
}

impl fmt::UpperHex for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.alternate() {
            write!(f, "0x")?;
        }
        write!(f, "{}", self.0.to_str_radix(16).to_uppercase())
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
        let mut s = "0x".to_owned();
        s.push_str(&format!("{:x}", self.0));
        serializer.serialize_str(&s)
    }
}

impl<'de> Deserialize<'de> for Uint256 {
    fn deserialize<D>(deserializer: D) -> Result<Uint256, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        let s = if s.starts_with("0x") { &s[2..] } else { &s };

        BigUint::from_str_radix(&s, 16)
            .map(Uint256)
            .map_err(serde::de::Error::custom)
    }
}

impl From<Int256> for Uint256 {
    fn from(n: Int256) -> Self {
        Uint256(n.0.to_biguint().unwrap())
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

macro_rules! uint_impl_from_int {
    ($T:ty) => {
        impl From<$T> for Uint256 {
            #[inline]
            fn from(n: $T) -> Self {
                Uint256(BigInt::from(n).to_biguint().unwrap())
            }
        }
    };
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

uint_impl_from_int!(i8);
uint_impl_from_int!(i16);
uint_impl_from_int!(i32);
uint_impl_from_int!(i64);
uint_impl_from_int!(isize);
uint_impl_from_uint!(u8);
uint_impl_from_uint!(u16);
uint_impl_from_uint!(u32);
uint_impl_from_uint!(u64);
uint_impl_from_uint!(u128);
uint_impl_from_uint!(usize);

impl<T> Add<T> for Uint256
where
    T: Into<Uint256>,
{
    type Output = Uint256;
    fn add(self, v: T) -> Uint256 {
        let num: Uint256 = v.into();
        if self.0.bits() + num.bits() > 256 {
            panic!("overflow");
        }
        Uint256(self.0 + num.0)
    }
}

impl<T> AddAssign<T> for Uint256
where
    T: Into<Uint256>,
{
    fn add_assign(&mut self, v: T) {
        self.0 = self.0.clone() + v.into().0;
        if self.0.bits() > 256 {
            panic!("overflow");
        }
    }
}

impl CheckedAdd for Uint256 {
    fn checked_add(&self, v: &Uint256) -> Option<Uint256> {
        // drop down to wrapped bigint to stop from panicing in fn above
        if self.0.bits() + v.0.bits() > 256 {
            return None;
        }
        Some(Uint256(self.0.clone() + v.0.clone()))
    }
}

impl<T> Sub<T> for Uint256
where
    T: Into<Uint256>,
{
    type Output = Uint256;
    fn sub(self, v: T) -> Uint256 {
        let num = self.0 - v.into().0;
        if num.bits() > 256 {
            panic!("overflow");
        }
        Uint256(num)
    }
}

impl<T> SubAssign<T> for Uint256
where
    T: Into<Uint256>,
{
    fn sub_assign(&mut self, v: T) {
        self.0 = self.0.clone() - v.into().0;
        if self.0.bits() > 256 {
            panic!("overflow");
        }
    }
}

impl CheckedSub for Uint256 {
    fn checked_sub(&self, v: &Uint256) -> Option<Uint256> {
        self.0.checked_sub(&v.0).map(Uint256)
    }
}

impl<T> Mul<T> for Uint256
where
    T: Into<Uint256>,
{
    type Output = Uint256;
    fn mul(self, v: T) -> Uint256 {
        let num = self.0 * v.into().0;
        if num.bits() > 256 {
            panic!("overflow");
        }
        Uint256(num)
    }
}

impl<T> MulAssign<T> for Uint256
where
    T: Into<Uint256>,
{
    fn mul_assign(&mut self, v: T) {
        self.0 = self.0.clone() * v.into().0;
        if self.0.bits() > 256 {
            panic!("overflow");
        }
    }
}

impl CheckedMul for Uint256 {
    fn checked_mul(&self, v: &Uint256) -> Option<Uint256> {
        // drop down to wrapped bigint to stop from panicing in fn above
        let num = self.0.clone() * v.0.clone();
        if num.bits() > 256 {
            return None;
        }
        Some(Uint256(num))
    }
}

impl<T> DivAssign<T> for Uint256
where
    T: Into<Uint256>,
{
    fn div_assign(&mut self, v: T) {
        self.0 = self.0.clone() / v.into().0;
        if self.0.bits() > 256 {
            panic!("overflow");
        }
    }
}

impl<T> Div<T> for Uint256
where
    T: Into<Uint256>,
{
    type Output = Uint256;
    fn div(self, v: T) -> Uint256 {
        let num = self.0 / v.into().0;
        if num.bits() > 256 {
            panic!("overflow");
        }
        Uint256(num)
    }
}

impl CheckedDiv for Uint256 {
    fn checked_div(&self, v: &Uint256) -> Option<Uint256> {
        if *v == Uint256::from(0) {
            return None;
        }
        // drop down to wrapped bigint to stop from panicing in fn above
        let num = self.0.clone() / v.0.clone();
        Some(Uint256(num))
    }
}

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
fn into_array() {
    let val = Uint256::from(1024u16);
    let foo: [u8; 32] = val.into();
    assert_eq!(
        foo,
        [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 4, 0
        ]
    );
}
