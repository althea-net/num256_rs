use num::bigint::{BigInt, ToBigInt};
use num::traits::ops::checked::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};
use num::traits::Signed;
use num::ToPrimitive;
use num::Zero;
use serde;
use serde::ser::Serialize;
use serde::{Deserialize, Deserializer, Serializer};
use std::fmt;
use std::ops::{Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::str::FromStr;

pub use uint256::Uint256;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Int256(pub BigInt);

impl Int256 {
    pub fn abs(&self) -> Self {
        Int256(self.clone().0.abs())
    }

    pub fn zero() -> Self {
        Int256(BigInt::zero())
    }
}

impl Deref for Int256 {
    type Target = BigInt;

    fn deref(&self) -> &BigInt {
        &self.0
    }
}

impl Neg for Int256 where {
    type Output = Int256;
    fn neg(self) -> Self::Output {
        let out = self.clone();
        Int256(out.0.to_bigint().unwrap() * -1)
    }
}

impl From<Uint256> for Int256 {
    fn from(n: Uint256) -> Self {
        if n.bits() > 255 {
            panic!("Overflow");
        }
        Int256(n.to_bigint().unwrap())
    }
}

macro_rules! impl_from_int {
    ($T:ty) => {
        impl From<$T> for Int256 {
            #[inline]
            fn from(n: $T) -> Self {
                Int256(BigInt::from(n))
            }
        }
    };
}

macro_rules! impl_from_uint {
    ($T:ty) => {
        impl From<$T> for Int256 {
            #[inline]
            fn from(n: $T) -> Self {
                Int256(BigInt::from(n))
            }
        }
    };
}

impl_from_int!(i8);
impl_from_int!(i16);
impl_from_int!(i32);
impl_from_int!(i64);
impl_from_int!(isize);
impl_from_uint!(u8);
impl_from_uint!(u16);
impl_from_uint!(u32);
impl_from_uint!(u64);
impl_from_uint!(usize);

macro_rules! impl_to {
    ($T:ty, $F:ident) => {
        impl Into<$T> for Int256 {
            #[inline]
            fn into(self) -> $T {
                (self.0).$F().unwrap()
            }
        }
    };
}

impl_to!(i8, to_i8);
impl_to!(i16, to_i16);
impl_to!(i32, to_i32);
impl_to!(i64, to_i64);
impl_to!(isize, to_isize);
impl_to!(u8, to_u8);
impl_to!(u16, to_u16);
impl_to!(u32, to_u32);
impl_to!(u64, to_u64);
impl_to!(usize, to_usize);

impl<'a> From<&'a Int256> for Int256 {
    fn from(n: &Int256) -> Int256 {
        n.clone()
    }
}

impl<'a> From<&'a Uint256> for Int256 {
    fn from(n: &Uint256) -> Int256 {
        n.clone().into()
    }
}

impl fmt::Display for Int256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.to_str_radix(10))
    }
}

impl fmt::Debug for Int256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Int256({})", self.to_string())
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

        BigInt::from_str(&s)
            .map(|v| Int256(v))
            .map_err(serde::de::Error::custom)
    }
}

impl<T> Add<T> for Int256
where
    T: Into<Int256>,
{
    type Output = Int256;
    fn add(self, v: T) -> Int256 {
        let num = self.0 + v.into().0;
        if num.bits() > 255 {
            panic!("overflow");
        }
        Int256(num)
    }
}

impl<T> AddAssign<T> for Int256
where
    T: Into<Int256>,
{
    fn add_assign(&mut self, v: T) {
        self.0 = self.0.clone() + v.into().0;
        if self.0.bits() > 255 {
            panic!("overflow");
        }
    }
}

impl CheckedAdd for Int256 {
    fn checked_add(&self, v: &Int256) -> Option<Int256> {
        // drop down to wrapped bigint to stop from panicing in fn above
        let num = self.0.clone() + v.0.clone();
        if num.bits() > 255 {
            return None;
        }
        Some(Int256(num))
    }
}

impl<T> Sub<T> for Int256
where
    T: Into<Int256>,
{
    type Output = Int256;
    fn sub(self, v: T) -> Int256 {
        let num = self.0 - v.into().0;
        if num.bits() > 255 {
            panic!("overflow");
        }
        Int256(num)
    }
}

impl<T> SubAssign<T> for Int256
where
    T: Into<Int256>,
{
    fn sub_assign(&mut self, v: T) {
        self.0 = self.0.clone() - v.into().0;
        if self.0.bits() > 255 {
            panic!("overflow");
        }
    }
}

impl CheckedSub for Int256 {
    fn checked_sub(&self, v: &Int256) -> Option<Int256> {
        // drop down to wrapped bigint to stop from panicing in fn above
        let num = self.0.clone() - v.0.clone();
        if num.bits() > 255 {
            return None;
        }
        Some(Int256(num))
    }
}

impl<T> Mul<T> for Int256
where
    T: Into<Int256>,
{
    type Output = Int256;
    fn mul(self, v: T) -> Int256 {
        let num = self.0 * v.into().0;
        if num.bits() > 255 {
            panic!("overflow");
        }
        Int256(num)
    }
}

impl<T> MulAssign<T> for Int256
where
    T: Into<Int256>,
{
    fn mul_assign(&mut self, v: T) {
        self.0 = self.0.clone() * v.into().0;
        if self.0.bits() > 255 {
            panic!("overflow");
        }
    }
}

impl CheckedMul for Int256 {
    fn checked_mul(&self, v: &Int256) -> Option<Int256> {
        // drop down to wrapped bigint to stop from panicing in fn above
        let num = self.0.clone() * v.0.clone();
        if num.bits() > 255 {
            return None;
        }
        Some(Int256(num))
    }
}

impl<T> DivAssign<T> for Int256
where
    T: Into<Int256>,
{
    fn div_assign(&mut self, v: T) {
        self.0 = self.0.clone() / v.into().0;
        if self.0.bits() > 255 {
            panic!("overflow");
        }
    }
}

impl<T> Div<T> for Int256
where
    T: Into<Int256>,
{
    type Output = Int256;
    fn div(self, v: T) -> Int256 {
        let num = self.0 / v.into().0;
        if num.bits() > 255 {
            panic!("overflow");
        }
        Int256(num)
    }
}

impl CheckedDiv for Int256 {
    fn checked_div(&self, v: &Int256) -> Option<Int256> {
        if *v == Int256::from(0) {
            return None;
        }
        // drop down to wrapped bigint to stop from panicing in fn above
        let num = self.0.clone() / v.0.clone();
        Some(Int256(num))
    }
}
