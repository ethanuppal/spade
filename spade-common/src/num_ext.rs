use num::{BigInt, BigUint, FromPrimitive};

pub trait InfallibleToBigInt {
    fn to_bigint(self) -> BigInt;
}

macro_rules! infallible_int_primitives {
    ($($ty:ty, $from_fn:ident);*) => {
        $(
            impl InfallibleToBigInt for $ty {
                fn to_bigint(self) -> BigInt {
                    num::BigInt::$from_fn(self).unwrap()
                }
            }
        )*
    }
}

infallible_int_primitives!(
    i8, from_i8;
    i16, from_i16;
    i32, from_i32;
    i64, from_i64;
    i128, from_i128;
    isize, from_isize;
    u8, from_u8;
    u16, from_u16;
    u32, from_u32;
    u64, from_u64;
    u128, from_u128;
    usize, from_usize
);

impl InfallibleToBigInt for &BigUint {
    fn to_bigint(self) -> BigInt {
        num::bigint::ToBigInt::to_bigint(self).unwrap()
    }
}
impl InfallibleToBigInt for BigUint {
    fn to_bigint(self) -> BigInt {
        num::bigint::ToBigInt::to_bigint(&self).unwrap()
    }
}

pub trait InfallibleToBigUint {
    fn to_biguint(self) -> BigUint;
}

macro_rules! infallible_uint_primitives {
    ($($ty:ty, $from_fn:ident);*) => {
        $(
            impl InfallibleToBigUint for $ty {
                fn to_biguint(self) -> BigUint {
                    num::BigUint::$from_fn(self).unwrap()
                }
            }
        )*
    }
}

infallible_uint_primitives!(
    u8, from_u8;
    u16, from_u16;
    u32, from_u32;
    u64, from_u64;
    u128, from_u128;
    usize, from_usize
);
