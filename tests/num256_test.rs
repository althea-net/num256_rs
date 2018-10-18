extern crate num256;
#[macro_use]
extern crate lazy_static;
extern crate num;
extern crate serde_json;
#[macro_use]
extern crate serde_derive;
extern crate serde;

use num::pow::pow;
use num::traits::cast::ToPrimitive;
use num::traits::ops::checked::{CheckedAdd, CheckedMul, CheckedSub};
use num::BigInt;
use num256::{Int256, Uint256};
use std::ops::{Add, Div, Sub};

lazy_static! {
    static ref BIGGEST_UINT: Uint256 = Uint256::from_bytes_le(&[255u8; 32]);
    static ref BIGGEST_INT: Int256 = Int256(pow(BigInt::from(2), 255) - BigInt::from(1));
    static ref SMALLEST_INT: Int256 = Int256(pow(BigInt::from(-2), 255) + BigInt::from(1));
    static ref BIGGEST_INT_AS_UINT: Uint256 = {
        let mut biggest_int_le = [255u8; 32];
        biggest_int_le[31] = 127;
        Uint256::from_bytes_le(&biggest_int_le)
    };
}

#[derive(Serialize, Deserialize, Debug)]
pub struct MyStruct {
    uint: Uint256,
    int: Int256,
}

#[test]
fn serialize() {
    let struc = MyStruct {
        uint: BIGGEST_UINT.clone(),
        int: SMALLEST_INT.clone(),
    };

    let expected = "{\"uint\":\"0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\",\"int\":\"-57896044618658097711785492504343953926634992332820282019728792003956564819967\"}";

    let j = serde_json::to_string(&struc).unwrap();

    assert_eq!(expected, j);
    let m: MyStruct = serde_json::from_str(expected).unwrap();

    assert_eq!(BIGGEST_UINT.clone(), m.uint);
    assert_eq!(SMALLEST_INT.clone(), m.int);
}

#[test]
fn test_from_uint() {
    let (a, b, c, d, e) = (
        Uint256::from(8 as u8),
        Uint256::from(8 as u16),
        Uint256::from(8 as u32),
        Uint256::from(8 as u64),
        Uint256::from(8 as usize),
    );

    assert_eq!(a, b);
    assert_eq!(b, c);
    assert_eq!(c, d);
    assert_eq!(d, e);
}

#[test]
fn test_from_int() {
    let (a, b, c, d, e) = (
        Int256::from(-8 as i8),
        Int256::from(-8 as i16),
        Int256::from(-8 as i32),
        Int256::from(-8 as i64),
        Int256::from(-8 as isize),
    );

    assert_eq!(a, b);
    assert_eq!(b, c);
    assert_eq!(c, d);
    assert_eq!(d, e);
}

#[test]
#[should_panic]
fn test_uint_add_panic() {
    let _val = BIGGEST_UINT.clone() + Uint256::from(1 as u32);
}

#[test]
fn test_uint_add_no_panic() {
    let _val = BIGGEST_UINT.clone() + Uint256::from(0 as u32);
}

#[test]
#[should_panic]
fn test_uint_from_add_panic() {
    let _val = BIGGEST_UINT.clone().add(Uint256::from(1));
}

#[test]
fn test_uint_from_add_no_panic() {
    let _val = BIGGEST_UINT.clone().add(Uint256::from(0));
}

#[test]
#[should_panic]
fn test_uint_sub_panic() {
    let _val = Uint256::from(1 as u32).sub(Uint256::from(2 as u32));
}

#[test]
fn test_uint_sub_no_panic() {
    assert_eq!(
        Uint256::from(1 as u32).sub(Uint256::from(1 as u32)),
        Uint256::from(0 as u32)
    );
}

#[test]
#[should_panic]
fn test_uint_from_sub_panic() {
    let _val = Uint256::from(1 as u32).sub(Uint256::from(2));
}

#[test]
fn test_uint_from_sub_no_panic() {
    assert_eq!(
        Uint256::from(1 as u32).sub(Uint256::from(1)),
        Uint256::from(0 as u32)
    );
}

#[test]
#[should_panic]
fn test_uint_mul_panic() {
    let _val: Uint256 = BIGGEST_UINT.clone() * Uint256::from(2);
}

#[test]
fn test_uint_mul_no_panic() {
    assert_eq!(Uint256::from(3) * Uint256::from(2), Uint256::from(6));
}

#[test]
#[should_panic]
fn test_uint_from_mul_panic() {
    let _val = BIGGEST_UINT.clone() * Uint256::from(2);
}

#[test]
fn test_uint_from_mul_no_panic() {
    assert_eq!(Uint256::from(3) * Uint256::from(2), Uint256::from(6));
}

#[test]
#[should_panic]
fn test_uint_div_panic() {
    let _val = BIGGEST_UINT.clone() / Uint256::from(0);
}

#[test]
fn test_uint_div_no_panic() {
    assert_eq!(Uint256::from(6) / Uint256::from(2), Uint256::from(3));
}

#[test]
fn test_uint_from_div_assign_no_panic() {
    assert_eq!(Uint256::from(6).div(Uint256::from(2)), Uint256::from(3));
}

#[test]
#[should_panic]
fn test_uint_from_div_panic() {
    let _val = BIGGEST_UINT.clone().div(Uint256::from(0));
}

#[test]
fn test_uint_from_div_no_panic() {
    assert_eq!(Uint256::from(6).div(Uint256::from(2)), Uint256::from(3));
}

#[test]
fn test_uint256() {
    assert!(
        BIGGEST_UINT.checked_add(&Uint256::from(1 as u32)).is_none(),
        "should return None adding 1 to biggest"
    );

    assert!(
        BIGGEST_UINT.checked_add(&Uint256::from(0 as u32)).is_some(),
        "should return Some adding 0 to biggest"
    );

    assert!(
        &Uint256::from(1 as u32)
            .checked_sub(&Uint256::from(2 as u32))
            .is_none(),
        "should return None if RHS is larger than LHS"
    );

    assert!(
        &Uint256::from(1 as u32)
            .checked_sub(&Uint256::from(1 as u32))
            .is_some(),
        "should return Some if RHS is not larger than LHS"
    );

    let num = &Uint256::from(1 as u32)
        .checked_sub(&Uint256::from(1 as u32))
        .unwrap()
        .to_u32()
        .unwrap();
    assert_eq!(*num, 0, "1 - 1 should = 0");

    let num2 = &Uint256::from(346 as u32)
        .checked_sub(&Uint256::from(23 as u32))
        .unwrap()
        .to_u32()
        .unwrap();

    assert_eq!(*num2, 323, "346 - 23 should = 323");
}

#[test]
#[should_panic]
fn test_int_add_panic() {
    let _val = BIGGEST_INT.clone() + Int256::from(1);
}

#[test]
fn test_int_add_no_panic() {
    let _val = BIGGEST_INT.clone() + Int256::from(0);
}

#[test]
#[should_panic]
fn test_int_sub_panic() {
    let _val = SMALLEST_INT.clone() - Int256::from(1);
}

#[test]
fn test_int_sub_no_panic() {
    assert_eq!(Int256::from(1) - Int256::from(1), Int256::from(0));
}

#[test]
#[should_panic]
fn test_int_mul_panic() {
    let _val = SMALLEST_INT.clone() * Int256::from(2);
}

#[test]
fn test_int_mul_no_panic() {
    assert_eq!(Int256::from(3) * Int256::from(2), Int256::from(6));
}

#[test]
#[should_panic]
fn test_int_div_panic() {
    let _val = SMALLEST_INT.clone() / Int256::from(0);
}

#[test]
fn test_int_div_no_panic() {
    assert_eq!(Int256::from(6) / Int256::from(2), Int256::from(3));
}

#[test]
#[should_panic]
fn test_int_from_add_panic() {
    let _val = BIGGEST_INT.clone() + 1;
}

#[test]
fn test_int_from_add_no_panic() {
    let _val = BIGGEST_INT.clone() + 0;
}

#[test]
#[should_panic]
fn test_int_from_sub_panic() {
    let _val = SMALLEST_INT.clone() - 1;
}

#[test]
fn test_int_from_sub_no_panic() {
    assert_eq!(Int256::from(1) - 1, Int256::from(0));
}

#[test]
#[should_panic]
fn test_int_from_mul_panic() {
    let _val = SMALLEST_INT.clone() * 2;
}

#[test]
fn test_int_from_mul_no_panic() {
    assert_eq!(Int256::from(3) * 2, Int256::from(6));
}

#[test]
#[should_panic]
fn test_int_from_div_panic() {
    let _val = SMALLEST_INT.clone() / 0;
}

#[test]
fn test_int_from_div_no_panic() {
    assert_eq!(Int256::from(6) / 2, Int256::from(3));
}

#[test]
#[should_panic]
fn test_uint_to_int_panic() {
    Int256::from(BIGGEST_INT_AS_UINT.clone().add(Uint256::from(1 as u32)));
}

#[test]
fn test_int256() {
    assert_eq!(
        Int256::from(BIGGEST_INT_AS_UINT.clone().add(Uint256::from(0 as u32))),
        BIGGEST_INT.clone()
    );

    assert!(
        BIGGEST_INT.checked_add(&Int256::from(1)).is_none(),
        "should return None adding 1 to biggest"
    );
    assert!(
        BIGGEST_INT.checked_add(&Int256::from(0)).is_some(),
        "should return Some adding 0 to biggest"
    );

    assert!(
        SMALLEST_INT.checked_sub(&Int256::from(1)).is_none(),
        "should return None subtracting 1 from smallest"
    );
    assert!(
        SMALLEST_INT.checked_sub(&Int256::from(0)).is_some(),
        "should return Some subtracting 0 from smallest"
    );

    assert!(SMALLEST_INT.checked_mul(&Int256::from(2)).is_none());
    assert!(SMALLEST_INT.checked_mul(&Int256::from(1)).is_some());

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
    value += 1;
    assert_eq!(value.bits(), 256);
}

#[test]
#[should_panic]
fn test_increment_2_to_the_power_of_256() {
    let mut value: Uint256 = "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
        .parse()
        .unwrap();
    assert_eq!(value.bits(), 256);
    value += 1;
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
    let value: Uint256 = 0.into();
    let res = value.checked_sub(&Uint256::from(1u32));
    assert!(res.is_none());
}

#[test]
#[should_panic]
fn test_uint_underflow_assign() {
    let mut value: Uint256 = 0.into();
    value -= 1;
}
