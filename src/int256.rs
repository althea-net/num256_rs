use num::bigint::BigInt;
use num::traits::ops::checked::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};
use num::traits::Signed;
use num::{pow, Bounded};
use serde::ser::Serialize;
use serde::{Deserialize, Deserializer, Serializer};
use std::fmt;
use std::ops::{
    Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::str::FromStr;

pub use crate::uint256::Uint256;

#[derive(
    Clone, PartialEq, Eq, PartialOrd, Ord, Hash, FromPrimitive, ToPrimitive, Zero, Default, One, Num,
)]
pub struct Int256(pub BigInt);

impl Int256 {
    /// Checked conversion to Uint256
    pub fn to_uint256(&self) -> Option<Uint256> {
        self.0
            .to_biguint()
            .map(Uint256)
            .filter(|value| *value <= Uint256::max_value() && *value >= Uint256::min_value())
    }
}

impl Bounded for Int256 {
    fn min_value() -> Self {
        lazy_static! {
            static ref MIN_VALUE: BigInt = -pow(BigInt::from(2), 255);
        }
        // -2**255
        Int256(MIN_VALUE.clone())
    }
    fn max_value() -> Self {
        lazy_static! {
            static ref MAX_VALUE: BigInt = pow(BigInt::from(2), 255) - BigInt::from(1);
        }
        Int256(MAX_VALUE.clone())
    }
}

impl Deref for Int256 {
    type Target = BigInt;

    fn deref(&self) -> &BigInt {
        &self.0
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

        BigInt::from_str(&s)
            .map(Int256)
            .map_err(serde::de::Error::custom)
    }
}

impl Signed for Int256 {
    fn abs(&self) -> Self {
        Int256(self.0.abs())
    }
    fn abs_sub(&self, other: &Self) -> Self {
        Int256(self.0.abs_sub(&other.0))
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

/// A macro that forwards an unary operator trait i.e. Add
macro_rules! forward_op {
    (impl $trait_: ident for $type_: ident { fn $method: ident }) => {
        impl $trait_<$type_> for $type_ {
            type Output = $type_;

            fn $method(self, $type_(b): $type_) -> $type_ {
                let $type_(a) = self;
                let res = $type_(a.$method(&b));
                if res > Int256::max_value() {
                    panic!("attempt to {} with overflow", stringify!($method));
                } else if res < Int256::min_value() {
                    panic!("attempt to {} with underflow", stringify!($method));
                } else {
                    res
                }
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
                    .filter(|value| value >= &Int256::min_value() && value <= &Int256::max_value())
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
                // Borrow happens only inside this scope
                {
                    let a = &mut self.0;
                    a.$method(b);
                }
                // Check bounds
                if *self > Int256::max_value() {
                    panic!("attempt to {} with overflow", stringify!($method));
                }
                if *self < Int256::min_value() {
                    panic!("attempt to {} with underflow", stringify!($method));
                }
            }
        }
    };
}

macro_rules! forward_unary_op {
    (impl $trait_: ident for $type_: ident { fn $method: ident }) => {
        impl $trait_ for $type_ {
            type Output = $type_;

            fn $method(self) -> $type_ {
                let $type_(a) = self;
                let res = $type_(a.$method());
                // Check bounds
                if res > Int256::max_value() {
                    panic!("attempt to {} with overflow", stringify!($method));
                }
                if res < Int256::min_value() {
                    panic!("attempt to {} with underflow", stringify!($method));
                }

                res
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

forward_unary_op! { impl Neg for Int256 { fn neg } }
