use crate::snapshot_error;

snapshot_error! {
    single_missing_enum_branch_errors,
    "
            enum X {
                A,
                B,
            }

            fn uwu(x: X) -> bool {
                match x {
                    X::A => true,
                }
            }
            "
}

snapshot_error! {
    multiple_missing_enum_branch_errors,
    "
            enum X {
                A,
                B,
                C,
                D,
            }

            fn uwu(x: X) -> bool {
                match x {
                    X::A => true,
                }
            }
            "
}

snapshot_error! {
    even_more_missing_enum_branch_errors,
    "
            enum X {
                A,
                B,
                C,
                D,
                E,
                F,
            }

            fn uwu(x: X) -> bool {
                match x {
                    X::A => true,
                }
            }
            "
}

snapshot_error! {
    missing_subpatterns_error_correctly,
    "
            enum X {
                A{a: bool},
                B
            }

            fn uwu(x: X) -> bool {
                match x {
                    X::B => true,
                }
            }

        "
}

snapshot_error! {
    missing_tuple_patterns_error_correctly,
    "
            enum X {
                A,
                B
            }

            fn uwu(x: (X, X)) -> bool {
                match x {
                    (X::A, X::A) => true,
                }
            }
        "
}

snapshot_error! {
    missing_tuple_patterns_error_correctly2,
    "
            enum X {
                A,
                B
            }

            fn uwu(x: (X, X)) -> bool {
                match x {
                    (X::A, X::A) => true,
                    (X::B, _) => true,
                }
            }
        "
}

snapshot_error! {
    missing_tuple_patterns_error_correctly3,
    "
            enum X {
                A,
                B
            }

            fn uwu(x: (X, X)) -> bool {
                match x {
                    (X::A, X::A) => true,
                    (X::A, X::B) => true,
                }
            }
        "
}

snapshot_error! {
    missing_inner_members_works,
    "
            enum X {
                A,
                B
            }

            enum Y {
                A{x1: X, x2: X},
            }

            fn uwu(y: Y) -> bool {
                match y {
                    Y::A(X::A, X::A) => true,
                }
            }
        "
}

snapshot_error! {
    missing_inner_members_works2,
    "
            enum X {
                A,
                B
            }

            enum Y {
                A{x1: X, x2: X},
            }

            fn uwu(y: Y) -> bool {
                match y {
                    Y::A(X::A, X::A) => true,
                    Y::A(X::A, _) => true,
                }
            }
        "
}

snapshot_error! {
    missing_boolean_patterns_work,
    "
            fn uwu(x: bool) -> bool {
                match x {
                    true => true,
                }
            }
        "
}

snapshot_error! {
    missing_struct_pattern_works,
    "
            struct A {x: bool, y: bool}

            fn uwu(a: A) -> bool {
                match a {
                    A(true, true) => true,
                }
            }
        "
}

snapshot_error! {
    missing_integer_patterns_reports_correctly,
    "
            fn uwu(a: int<8>) -> bool {
                match a {
                    0 => true,
                }
            }
            "
}

snapshot_error! {
    missing_integer_patterns_reports_correctly2,
    "
            fn uwu(a: int<8>) -> bool {
                match a {
                    0 => true,
                    1 => true,
                    4 => true,
                }
            }
            "
}