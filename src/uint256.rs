use num::traits::ops::checked::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};
use num::Num;
use num::{BigInt, BigUint};
use serde;
use serde::ser::Serialize;
use serde::{Deserialize, Deserializer, Serializer};
use std::fmt;
use std::ops::{Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;

pub use super::Int256;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Uint256(pub BigUint);

impl Uint256 {
    pub fn from_bytes_le(slice: &[u8]) -> Uint256 {
        Uint256(BigUint::from_bytes_le(slice))
    }
}

impl FromStr for Uint256 {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        BigUint::from_str(s)
            .map(Uint256)
            .map_err(|e| format!("{:?}", e))
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
        if self.0.bits() > 255 {
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
        if num.bits() > 255 {
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
        if self.0.bits() > 255 {
            panic!("overflow");
        }
    }
}

impl CheckedSub for Uint256 {
    fn checked_sub(&self, v: &Uint256) -> Option<Uint256> {
        if self.0.bits().checked_sub(v.0.bits()).is_none() {
            return None;
        }
        Some(Uint256(self.0.clone() - v.0.clone()))
    }
}

impl<T> Mul<T> for Uint256
where
    T: Into<Uint256>,
{
    type Output = Uint256;
    fn mul(self, v: T) -> Uint256 {
        let num = self.0 * v.into().0;
        if num.bits() > 255 {
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
        if self.0.bits() > 255 {
            panic!("overflow");
        }
    }
}

impl CheckedMul for Uint256 {
    fn checked_mul(&self, v: &Uint256) -> Option<Uint256> {
        // drop down to wrapped bigint to stop from panicing in fn above
        let num = self.0.clone() * v.0.clone();
        if num.bits() > 255 {
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
        if self.0.bits() > 255 {
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
        if num.bits() > 255 {
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
