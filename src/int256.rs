use num::{BigInt, BigUint, Bounded, FromPrimitive, Zero};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use std::{fmt, ops::Deref, str::FromStr};

/// A 256-bit newtype wrapper for `num::BigInt`
#[derive(
    Clone, PartialEq, Eq, PartialOrd, Ord, FromPrimitive, ToPrimitive, Num, NumOps, Zero, One,
)]
pub struct Int256(pub BigInt);

impl Bounded for Int256 {
    // An n-wide binary number's 2's complement boundaries present like so:
    // max(n)  =  2^(n-1)-1
    // min(n)  = -2^(n-1)
    fn min_value() -> Self {
        Int256(BigInt::zero() - num::checked_pow(2, 255).unwrap())
    }
    fn max_value() -> Self {
        Int256(num::checked_pow(2, 255).unwrap() - BigInt::from_u64(1).unwrap())
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

impl Deref for Int256 {
    type Target = BigInt;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

