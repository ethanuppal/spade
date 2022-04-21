use std::collections::HashMap;

use itertools::Itertools;
use num::{
    bigint::{Sign, ToBigUint},
    BigInt, BigUint,
};
use spade_hir_lowering::MirLowerable;
use spade_mir::{codegen::escape_path, ValueName};
use spade_typeinference::equation::TypedExpression;
use spade_types::{ConcreteType, PrimitiveType};
use vcd::Value;

pub fn translate_names(
    input: HashMap<TypedExpression, Option<ConcreteType>>,
) -> HashMap<String, Option<ConcreteType>> {
    input
        .into_iter()
        .map(|(key, value)| {
            let name = match key {
                TypedExpression::Id(id) => ValueName::Expr(id).var_name(),
                TypedExpression::Name(name_id) => {
                    escape_path(ValueName::Named(name_id.0, name_id.1.to_string()).var_name())
                }
            };
            (name, value)
        })
        .collect()
}

#[derive(Debug, PartialEq, Hash, Eq)]
enum MaybeValue<T> {
    Value(T),
    Undef,
    HighImpedance,
}

impl<T> MaybeValue<T> {
    fn map<F, U>(self, f: F) -> MaybeValue<U>
    where
        F: Fn(T) -> U,
    {
        match self {
            MaybeValue::Value(t) => MaybeValue::Value(f(t)),
            MaybeValue::Undef => MaybeValue::Undef,
            MaybeValue::HighImpedance => MaybeValue::HighImpedance,
        }
    }
}

impl<T> std::fmt::Display for MaybeValue<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeValue::Value(v) => write!(f, "{v}"),
            MaybeValue::Undef => write!(f, "UNDEF"),
            MaybeValue::HighImpedance => write!(f, "HIGHIMP"),
        }
    }
}

fn translate_uint(value: &[Value], flip: bool) -> MaybeValue<BigUint> {
    let mut result = BigUint::new(vec![0]);
    for v in value {
        if v == &Value::X {
            return MaybeValue::Undef;
        } else if v == &Value::Z {
            return MaybeValue::HighImpedance;
        }
        if !flip {
            if v == &Value::V1 {
                result = (result << 1i32) + BigUint::new(vec![1]);
            } else {
                result <<= 1i32
            }
        } else {
            if v == &Value::V0 {
                result = (result << 1i32) + BigUint::new(vec![1]);
            } else {
                result <<= 1i32
            }
        }
    }
    MaybeValue::Value(result)
}

/// Translate a signed integer into a BigInt if none of the elements are undefined
/// if not returns Undef
///
/// The values must be in two's complement form and of the intended width of the
/// integer. I.e. the leftmost bit is interpreted as the sign bit
fn translate_signed_int(value: &[Value]) -> MaybeValue<BigInt> {
    if value.contains(&Value::X) {
        MaybeValue::Undef
    } else if value.contains(&Value::Z) {
        MaybeValue::HighImpedance
    } else {
        let negative = value[0] == Value::V1;
        let uint_val = translate_uint(&value[1..], negative);
        if negative {
            uint_val.map(|uint| {
                BigInt::from_biguint(Sign::Minus, uint + ToBigUint::to_biguint(&1).unwrap())
            })
        } else {
            uint_val.map(|uint| BigInt::from_biguint(Sign::Plus, uint))
        }
    }
}

fn inner_translate_value(in_value: &[Value], t: &ConcreteType) -> String {
    let value_len = in_value.len();
    let type_size = t.to_mir_type().size();
    let missing_values = type_size as usize - value_len;

    // Extend according to verilog specification section 18.2.2
    let extend_value = match in_value[0] {
        Value::V0 => Value::V0,
        Value::V1 => Value::V0,
        Value::X => Value::X,
        Value::Z => Value::Z,
    };

    let value = [&vec![extend_value; missing_values], in_value].concat();

    match t {
        ConcreteType::Tuple(inner) => {
            let mut offset = 0;
            let values = inner
                .iter()
                .map(|t| {
                    let end = offset + t.to_mir_type().size() as usize;
                    let result = inner_translate_value(&value[offset..end], t);
                    offset = end;
                    result
                })
                .collect::<Vec<_>>()
                .join(",");

            format!("({values})")
        }
        ConcreteType::Struct { members } => {
            let mut offset = 0;
            let values = members
                .iter()
                .map(|(name, t)| {
                    let end = offset + t.to_mir_type().size() as usize;
                    let result =
                        format!("{name}:{}", inner_translate_value(&value[offset..end], t));
                    offset = end;
                    result
                })
                .join(",");

            format!("{{{values}}}")
        }
        ConcreteType::Array { inner, size } => {
            let mut offset = 0;
            let values = (0..*size)
                .map(|_| {
                    let end = offset + inner.to_mir_type().size() as usize;
                    let result = inner_translate_value(&value[offset..end], inner);
                    offset = end;
                    result
                })
                .join(",");
            format!("[{values}]")
        }
        ConcreteType::Enum { options } => {
            let tag_size = (options.len() as f32).log2().ceil() as usize;
            let tag = translate_uint(&value[0..tag_size], false);
            match tag {
                MaybeValue::Value(val) => {
                    let tag_digits = val.to_u64_digits();
                    if tag_digits.len() > 1 {
                        panic!("Tag digit count must be 1, was {}", tag_digits.len());
                    } else {
                        let tag = tag_digits.get(0).cloned().unwrap_or(0);
                        if tag >= options.len() as u64 {
                            format!("?TAG?")
                        } else {
                            let variant_idx = tag as usize;
                            let (variant_name, inner_types) = &options[variant_idx];

                            let mut offset = tag_size;
                            let inner = inner_types
                                .iter()
                                .map(|t| {
                                    let end = offset + t.to_mir_type().size() as usize;
                                    let result = inner_translate_value(&value[offset..end], t);
                                    offset = end;
                                    result
                                })
                                .join(",");

                            format!("{variant_name}({inner})")
                        }
                    }
                }
                MaybeValue::Undef => format!("UNDEF"),
                MaybeValue::HighImpedance => format!("HIGHIMP"),
            }
        }
        ConcreteType::Single {
            base: PrimitiveType::Bool,
            params: _,
        }
        | ConcreteType::Single {
            base: PrimitiveType::Clock,
            params: _,
        } => match value[0] {
            Value::V0 => "0".to_string(),
            Value::V1 => "1".to_string(),
            Value::X => "UNDEF".to_string(),
            Value::Z => "HIGHIMP".to_string(),
        },
        ConcreteType::Single {
            base: PrimitiveType::Int,
            params: _,
        } => format!("{}", translate_signed_int(&value)),
        ConcreteType::Single {
            base: PrimitiveType::Uint,
            params: _,
        } => format!("{}", translate_uint(&value, false)),
        ConcreteType::Single {
            base: PrimitiveType::Memory,
            params: _,
        } => format!("memory"),
        ConcreteType::Integer(_) => {
            panic!("Found a variable with type level integer in the vcd file")
        }
    }
}

pub fn translate_value(
    name: &str,
    value: &[Value],
    types: &HashMap<String, Option<ConcreteType>>,
) -> Option<String> {
    // Try to translate the name back into a name_id
    if let Some(Some(t)) = types.get(name) {
        Some(inner_translate_value(value, t))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use num::bigint::ToBigInt;
    use spade_common::name::testutil::name_id;

    use super::*;

    use spade_ast::testutil::ast_ident;

    use Value::{V0, V1, X, Z};

    #[test]
    fn positive_integers_parse_correctly() {
        let values = vec![V0, V1, V0, V1, V1];

        let translated = translate_signed_int(&values);

        assert_eq!(
            translated,
            MaybeValue::Value(BigInt::new(Sign::Plus, vec![0b1011]))
        );
    }

    #[test]
    fn negative_integers_parse_correctly() {
        let values = vec![V1, V1, V0, V1, V1];
        // -16 + 8 + 0  + 2 + 1 = -5

        let translated = translate_signed_int(&values);

        assert_eq!(
            translated,
            MaybeValue::Value(ToBigInt::to_bigint(&-5).unwrap())
        );
    }

    #[test]
    fn large_positive_unsigned_integers_parse_correctly() {
        let mut values = vec![Value::V1];
        values.append(&mut vec![Value::V0; 32]);

        let translated = translate_uint(&values, false);

        assert_eq!(
            translated,
            MaybeValue::Value(ToBigUint::to_biguint(&0x10000_0000u64).unwrap())
        )
    }

    #[test]
    fn struct_translation_works() {
        let ty = ConcreteType::Struct {
            members: vec![
                (
                    ast_ident("a").inner,
                    ConcreteType::Single {
                        base: PrimitiveType::Int,
                        params: vec![ConcreteType::Integer(5)],
                    },
                ),
                (
                    ast_ident("b").inner,
                    ConcreteType::Single {
                        base: PrimitiveType::Int,
                        params: vec![ConcreteType::Integer(3)],
                    },
                ),
            ],
        };

        let value = vec![/*a*/ V0, V1, V0, V0, V0, /*b*/ V1, V0, V0];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "{a:8,b:-4}");
    }

    #[test]
    fn tuple_translation_works() {
        let ty = ConcreteType::Tuple(vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5)],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3)],
            },
        ]);

        let value = vec![/*a*/ V0, V1, V0, V0, V1, /*b*/ V1, V0, V1];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "(9,-3)");
    }

    #[test]
    fn tuple_translation_of_undef_works() {
        let ty = ConcreteType::Tuple(vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5)],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3)],
            },
        ]);

        let value = vec![/*a*/ X, X, X, X, /*b*/ X, X, X];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "(UNDEF,UNDEF)");
    }

    fn enum_ty() -> ConcreteType {
        let ty0 = vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5)],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3)],
            },
        ];
        let ty1 = vec![ConcreteType::Single {
            base: PrimitiveType::Int,
            params: vec![ConcreteType::Integer(3)],
        }];

        ConcreteType::Enum {
            options: vec![
                (name_id(0, "A").inner, ty0),
                (name_id(0, "B").inner, ty1),
                (name_id(0, "C").inner, vec![]),
            ],
        }
    }

    #[test]
    fn enum_translation_works_full_width() {
        let ty = enum_ty();

        let value = vec![
            /*tag*/ V0, V0, /*a*/ V0, V1, V0, V0, V1, /*b*/ V1, V0, V1,
        ];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "A(9,-3)");
    }

    #[test]
    fn enum_translation_works_half_width() {
        let ty = enum_ty();

        let value = vec![
            /*tag*/ V0, V1, /*payload*/ V0, V1, V0, /*padding*/ X, X, X, X, X,
        ];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "B(2)");
    }

    #[test]
    fn enum_translation_works_zero_width() {
        let ty = enum_ty();

        let value = vec![/*tag*/ V1, V0, /*payload*/ X, X, X, X, X, X, X, X];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "C()");
    }

    #[test]
    fn enum_translation_of_undef_is_undef() {
        let ty = enum_ty();

        let value = vec![/*tag*/ X, X, /*payload*/ X, X, X, X, X, X, X, X];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "UNDEF");
    }

    #[test]
    fn enum_translation_works_unknown_tag() {
        let ty = enum_ty();

        let value = vec![
            /*tag*/ V1, V1, /*a*/ X, X, X, X, X, /*b*/ X, X, X,
        ];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "?TAG?");
    }

    #[test]
    fn array_translation_works() {
        let ty = ConcreteType::Array {
            inner: Box::new(ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3)],
            }),
            size: 2,
        };

        let value = vec![V0, V0, V1, V0, V1, V0];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "[1,2]");
    }

    #[test]
    fn extending_x_extends_with_more_undef() {
        let ty = ConcreteType::Tuple(vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5)],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3)],
            },
        ]);

        let value = vec![X];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "(UNDEF,UNDEF)");
    }

    #[test]
    fn extending_z_extends_with_more_undef() {
        let ty = ConcreteType::Tuple(vec![
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(5)],
            },
            ConcreteType::Single {
                base: PrimitiveType::Int,
                params: vec![ConcreteType::Integer(3)],
            },
        ]);

        let value = vec![Z];
        let translated = inner_translate_value(&value, &ty);

        assert_eq!(translated, "(HIGHIMP,HIGHIMP)");
    }
}
