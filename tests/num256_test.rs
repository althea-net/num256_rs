extern crate num256;
#[macro_use]
extern crate lazy_static;
extern crate serde_json;
#[macro_use]
extern crate serde_derive;
extern crate serde;

use num256::{Int256, Uint256};
use num_traits::{Bounded, CheckedAdd, CheckedMul, CheckedSub, Signed, ToPrimitive, Zero};
use std::ops::{Add, Div, Sub};

lazy_static! {
    static ref BIGGEST_UINT: Uint256 = Uint256::max_value();
    static ref BIGGEST_INT_AS_UINT: Uint256 = Int256::max_value().to_uint256().unwrap();
}

#[derive(Serialize, Deserialize, Debug)]
pub struct MyStruct {
    uint: Uint256,
    int: Int256,
}

#[test]
fn serialize() {
    let struc = MyStruct {
        uint: *BIGGEST_UINT,
        int: Int256::min_value(),
    };

    let expected = r#"{"uint":"115792089237316195423570985008687907853269984665640564039457584007913129639935","int":"-57896044618658097711785492504343953926634992332820282019728792003956564819968"}"#;

    let j = serde_json::to_string(&struc).unwrap();

    assert_eq!(expected, j);
    let m: MyStruct = serde_json::from_str(expected).unwrap();

    assert_eq!(BIGGEST_UINT.clone(), m.uint);
    assert_eq!(Int256::min_value(), m.int);
}

#[test]
fn serialize_from_hex() {
    let expected = r#"{"uint":"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff","int":"-57896044618658097711785492504343953926634992332820282019728792003956564819968"}"#;
    let m: MyStruct = serde_json::from_str(expected).unwrap();

    assert_eq!(BIGGEST_UINT.clone(), m.uint);
    assert_eq!(Int256::min_value(), m.int);
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_from_uint() {
    let (a, b, c, d, e) = (
        Uint256::from(8u8),
        Uint256::from(8u16),
        Uint256::from(8u32),
        Uint256::from(8u64),
        Uint256::from(8usize),
    );

    assert_eq!(a, b);
    assert_eq!(b, c);
    assert_eq!(c, d);
    assert_eq!(d, e);
}

#[test]
#[should_panic]
fn test_from_uint_to_int() {
    let uint = *BIGGEST_UINT;
    let _res = uint.to_int256().unwrap();
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_from_int() {
    let (a, b, c, d, e) = (
        Int256::from(-8i8),
        Int256::from(-8i16),
        Int256::from(-8i32),
        Int256::from(-8i64),
        Int256::from(-8isize),
    );

    assert_eq!(a, b);
    assert_eq!(b, c);
    assert_eq!(c, d);
    assert_eq!(d, e);
}

#[test]
#[should_panic]
fn test_uint_add_panic() {
    let _val = *BIGGEST_UINT + Uint256::from(1u32);
}

#[test]
#[should_panic]
fn test_uint_add_assign_panic() {
    let mut val = *BIGGEST_UINT;
    val += Uint256::from(1u32);
}

#[test]
fn test_uint_add_no_panic() {
    let _val = *BIGGEST_UINT + Uint256::from(0u32);
}

#[test]
#[should_panic]
fn test_uint_from_add_panic() {
    let _val = (*BIGGEST_UINT).add(Uint256::from(1u8));
}

#[test]
fn test_uint_from_add_no_panic() {
    let _val = (*BIGGEST_UINT).add(Uint256::zero());
}

#[test]
#[should_panic]
fn test_uint_sub_panic() {
    let _val = Uint256::from(1u32).sub(Uint256::from(2u32));
}

#[test]
fn test_uint_sub_no_panic() {
    assert_eq!(
        Uint256::from(1u32).sub(Uint256::from(1u32)),
        Uint256::from(0u32)
    );
}

#[test]
#[should_panic]
fn test_uint_from_sub_panic() {
    let _val = Uint256::from(1u32).sub(Uint256::from(2u8));
}

#[test]
fn test_uint_from_sub_no_panic() {
    assert_eq!(
        Uint256::from(1u32).sub(Uint256::from(1u8)),
        Uint256::from(0u32)
    );
}

#[test]
#[should_panic]
fn test_uint_mul_panic() {
    let _val: Uint256 = *BIGGEST_UINT * Uint256::from(2u8);
}

#[test]
fn test_uint_mul_no_panic() {
    assert_eq!(Uint256::from(3u8) * Uint256::from(2u8), Uint256::from(6u8));
    assert_eq!(
        "57896044618658097711785492504343953926634992332820282019728792003956564819967"
            .parse::<Uint256>()
            .unwrap()
            * Uint256::from(2u8),
        "115792089237316195423570985008687907853269984665640564039457584007913129639934"
            .parse::<Uint256>()
            .unwrap()
    );
}

#[test]
#[should_panic]
fn test_uint_from_mul_panic() {
    let _val = *BIGGEST_UINT * Uint256::from(2u8);
}

#[test]
#[should_panic]
fn test_uint_from_mul_assign_panic() {
    let mut val = *BIGGEST_UINT;
    val *= Uint256::from(2u8);
}

#[test]
fn test_uint_from_mul_no_panic() {
    assert_eq!(Uint256::from(3u8) * Uint256::from(2u8), Uint256::from(6u8));
}

#[test]
#[should_panic]
fn test_uint_div_panic() {
    let _val = *BIGGEST_UINT / Uint256::zero();
}

#[test]
fn test_uint_div_no_panic() {
    assert_eq!(Uint256::from(6u8) / Uint256::from(2u8), Uint256::from(3u8));
}

#[test]
#[should_panic]
fn test_uint_from_div_panic() {
    let _val = (*BIGGEST_UINT).div(Uint256::from(0u8));
}

#[test]
fn test_uint_from_checked_div() {
    assert!(BIGGEST_UINT
        .clone()
        .checked_div(*Uint256::from(0u8))
        .is_none());
    assert!(BIGGEST_UINT
        .clone()
        .checked_div(*Uint256::from(5u8))
        .is_some());
}

#[test]
fn test_uint_from_div_no_panic() {
    assert_eq!(
        Uint256::from(6u8).div(Uint256::from(2u8)),
        Uint256::from(3u8)
    );
}

#[test]
fn test_uint_from_div_assign_no_panic() {
    let mut value = Uint256::from(6u8);
    value /= 2u8.into();
    assert_eq!(value, 3u8.into());
}

#[test]
fn test_uint256() {
    assert_eq!(BIGGEST_UINT.bits(), 256);
    assert!(
        BIGGEST_UINT.checked_add(&Uint256::from(1u32)).is_none(),
        "should return None adding 1 to biggest"
    );

    assert!(
        BIGGEST_UINT.checked_add(&Uint256::from(0u32)).is_some(),
        "should return Some adding 0 to biggest"
    );

    assert!(
        &Uint256::from(1u32)
            .checked_sub(&Uint256::from(2u32))
            .is_none(),
        "should return None if RHS is larger than LHS"
    );

    assert!(
        &Uint256::from(1u32)
            .checked_sub(&Uint256::from(1u32))
            .is_some(),
        "should return Some if RHS is not larger than LHS"
    );

    let num = &Uint256::from(1u32)
        .checked_sub(&Uint256::from(1u32))
        .unwrap()
        .to_u32()
        .unwrap();
    assert_eq!(*num, 0, "1 - 1 should = 0");

    let num2 = &Uint256::from(346u32)
        .checked_sub(&Uint256::from(23u32))
        .unwrap()
        .to_u32()
        .unwrap();

    assert_eq!(*num2, 323, "346 - 23 should = 323");
}

#[test]
#[should_panic]
fn test_int_add_panic() {
    let _val = Int256::max_value() + Int256::from(1);
}

#[test]
fn test_int_add_no_panic() {
    let _val = Int256::max_value() + Int256::from(0);
}

#[test]
#[should_panic]
fn test_int_sub_panic() {
    let _val = Int256::min_value() - Int256::from(1);
}

#[test]
#[should_panic]
fn test_int_assign_sub_panic() {
    let mut val = Int256::min_value();
    val -= Int256::from(1);
}

#[test]
fn test_int_sub_no_panic() {
    assert_eq!(Int256::from(1) - Int256::from(1), Int256::from(0));
}

#[test]
#[should_panic]
fn test_int_mul_panic() {
    let _val = Int256::min_value() * Int256::from(2);
}

#[test]
fn test_int_mul_no_panic() {
    assert_eq!(Int256::from(3) * Int256::from(2), Int256::from(6));
}

#[test]
#[should_panic]
fn test_int_div_panic() {
    let _val = Int256::min_value() / Int256::from(0);
}

#[test]
fn test_int_div_no_panic() {
    assert_eq!(Int256::from(6) / Int256::from(2), Int256::from(3));
}

#[test]
#[should_panic]
fn test_int_from_add_panic() {
    let _val = Int256::max_value() + 1.into();
}

#[test]
fn test_int_from_add_no_panic() {
    let _val = Int256::max_value() + 0.into();
}

#[test]
#[should_panic]
fn test_int_from_sub_panic() {
    let _val = Int256::min_value() - 1.into();
}

#[test]
fn test_int_from_sub_no_panic() {
    assert_eq!(Int256::from(1) - 1.into(), Int256::from(0));
}

#[test]
#[should_panic]
fn test_int_from_mul_panic() {
    let _val = Int256::min_value() * 2.into();
}

#[test]
fn test_int_from_mul_no_panic() {
    assert_eq!(Int256::from(3) * 2.into(), Int256::from(6));
}

#[test]
#[should_panic]
fn test_int_from_div_panic() {
    let _val = Int256::min_value() / 0.into();
}

#[test]
fn test_int_from_div_no_panic() {
    assert_eq!(Int256::from(6) / 2.into(), Int256::from(3));
}

#[test]
#[should_panic]
fn test_uint_to_int_panic() {
    BIGGEST_UINT.clone().to_int256().unwrap();
}

#[test]
fn test_int256() {
    assert_eq!(Int256::max_value() + Int256::zero(), Int256::max_value());

    assert!(
        Int256::max_value().checked_add(&Int256::from(1)).is_none(),
        "should return None adding 1 to biggest"
    );
    assert!(
        Int256::max_value().checked_add(&Int256::from(0)).is_some(),
        "should return Some adding 0 to biggest"
    );

    assert!(
        Int256::min_value().checked_sub(&Int256::from(1)).is_none(),
        "should return None subtracting 1 from smallest"
    );
    assert!(
        Int256::min_value().checked_sub(&Int256::from(0)).is_some(),
        "should return Some subtracting 0 from smallest"
    );

    assert!(Int256::min_value().checked_mul(&Int256::from(2)).is_none());
    assert!(Int256::min_value().checked_mul(&Int256::from(1)).is_some());

    let num = &Int256::from(345)
        .checked_sub(&Int256::from(44))
        .unwrap()
        .to_u32()
        .unwrap();

    assert_eq!(*num, 301, "345 - 44 should = 301");
}

#[test]
fn test_increment_2_to_the_power_of_255() {
    // This one was failing with ethereum_types::U256
    let mut value: Uint256 = "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
        .parse()
        .unwrap();
    assert_eq!(value.bits(), 255);
    value += 1u8.into();
    assert_eq!(value.bits(), 256);
}

#[test]
#[should_panic]
fn test_increment_2_to_the_power_of_256() {
    let mut value: Uint256 = "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
        .parse()
        .unwrap();
    assert_eq!(value.bits(), 256);
    value += 1u8.into();
    assert_eq!(value.bits(), 256);
}

#[test]
fn test_increment_2_to_the_power_of_256_checked() {
    //2**256-1
    let value: Uint256 = "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
        .parse()
        .unwrap();
    assert_eq!(value.bits(), 256);
    assert!(value.checked_add(&Uint256::from(1u32)).is_none());
}

#[test]
fn test_uint_underflow() {
    let value: Uint256 = Uint256::zero();
    let res = value.checked_sub(&Uint256::from(1u32));
    assert!(res.is_none());
}

#[test]
#[should_panic]
fn test_uint_underflow_assign() {
    let mut value: Uint256 = Uint256::zero();
    value -= 1u8.into();
}

#[test]
fn test_negate() {
    let value: Int256 = 1i32.into();
    let new_value = -value;
    assert_eq!(new_value, Int256::from(-1i32));
}

#[test]
#[should_panic]
fn test_uint_to_int() {
    let value = *BIGGEST_UINT;
    value.to_int256().unwrap();
}

#[test]
fn test_int_to_uint() {
    let value = Int256::max_value();
    value.to_uint256().unwrap();
}

#[test]
fn test_biggest_unsigned_to_int() {
    let _val0: Int256 = 255u8.into();
    let _val1: Int256 = 65_535u16.into();
    let _val2: Int256 = 4_294_967_295u32.into();
    let _val3: Int256 = 18_446_744_073_709_551_615u64.into();
    let _val4: Int256 = 340_282_366_920_938_463_463_374_607_431_768_211_455u128.into();
}

#[test]
fn test_abs() {
    // if we don't subtract a small number we will overflow since Uint256 max
    // is one smaller than min
    let very_small: Int256 = Int256::min_value() + 50.into();
    let abs = very_small.abs();
    let _very_large: Uint256 = abs.to_uint256().unwrap();
}
