use num::{BigUint, Bounded, Num, Zero};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use std::{fmt, ops::Deref, str::FromStr};

/// A 256-bit newtype wrapper for `num::BigUint`
#[derive(Clone, PartialEq, PartialOrd, FromPrimitive, ToPrimitive, Num, NumOps, Zero, One)]
pub struct Uint256(pub BigUint);

impl Bounded for Uint256 {
    fn min_value() -> Self {
        Self::zero()
    }
    fn max_value() -> Self {
        // BigUint's constructor takes a big-endian vec of base 2^32 digits.
        Uint256(BigUint::new(vec![std::u32::MAX; 8]))
    }
}

impl fmt::Display for Uint256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.0)
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

impl Deref for Uint256 {
    type Target = BigUint;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
