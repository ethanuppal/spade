use crate::{build_items, snapshot_error};

snapshot_error! {
    double_consumption_of_identifier_produces_error,
    "
    entity x(resource: &mut bool) -> (&mut bool, &mut bool) {
        (resource, resource)
    }
    "
}

snapshot_error! {
    double_consumption_of_identifier_produces_error_in_array,
    "
    entity x(resource: &mut bool) -> [&mut bool; 2] {
        [resource, resource]
    }
    "
}

snapshot_error! {
    double_consumption_of_identifier_in_pipeline_produces_error,
    "
    pipeline(0) x(clk: clk, resource: &mut bool) -> (&mut bool, &mut bool) {
        (resource, resource)
    }
    "
}

snapshot_error! {
    unused_resource_causes_error,
    "
    entity x(resource: &mut bool) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_field_causes_error,
    "
    struct port A {
        x: &mut bool,
        y: &bool
    }
    entity x(resource: A) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_transitive_field_causes_error,
    "
    struct port A {
        x: &mut bool,
        y: &bool
    }
    struct port B {
        a: A
    }
    entity x(resource: B) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_tuple_member_causes_error,
    "
    entity x(resource: (&mut bool, &bool)) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_transitive_tuple_member_causes_error,
    "
    entity x(resource: ((&mut bool, &bool), &bool)) -> bool {
        true
    }
    "
}

snapshot_error! {
    unused_anonymous_expression_is_reported,
    "
    entity producer() -> (&mut bool, &mut bool) __builtin__
    entity consumer(x: &mut bool) -> bool __builtin__

    entity x() -> bool {
        inst consumer(inst producer()#0)
    }
    "
}

snapshot_error! {
    double_tuple_consumption_causes_error,
    "
    entity x(resource: (&mut bool, &bool)) -> (&mut bool, &mut bool) {
        (resource#0, resource#0)
    }
    "
}

snapshot_error! {
    more_than_one_field_consumption_causes_error,
    "
    struct port A {
        x: &mut bool,
    }
    entity x(a: A) -> (&mut bool, &mut bool) {
        (a.x, a.x)
    }
    "
}

snapshot_error! {
    consuming_a_field_produces_an_error_when_consuming_whole_struct,
    "
    struct port A {
        x: &mut bool,
    }

    entity consumer(a: &mut bool) -> bool __builtin__

    entity x(a: A) -> A {
        let _ = inst consumer(a.x);
        a
    }
    "
}

snapshot_error! {
    destructuring_linear_type_requires_use_of_subtypes,
    "
    entity x(a: (&mut bool, &mut bool)) -> &mut bool {
        let (x, y) = a;
        x
    }
    "
}

snapshot_error! {
    using_a_single_linear_field_does_not_use_the_whole_struct,
    "
    struct port A {
        a: &mut bool,
        b: &mut bool,
    }
    entity x(a: A) -> &mut bool {
        a.a
    }
    "
}

#[test]
fn linear_checking_on_registers_works() {
    let code = "
    entity test(clk: clk) -> int<8> {
        reg(clk) x = x;
        x
    }
    ";
    build_items(code);
}

snapshot_error! {
    checking_works_with_decld_value,
    "
    entity make_port() -> &mut bool __builtin__
    entity consume(p: &mut bool) -> bool __builtin__

    entity test() -> bool {
        decl x;
        let _ = inst consume(x);
        let x = inst make_port();
        let _ = inst consume(x);
        true
    }
    "
}

snapshot_error! {
    function_calls_consume_ports,
    "
        entity make_port() -> &mut bool __builtin__

        entity consumer(x: &mut bool) -> bool __builtin__

        entity test() -> (bool, bool) {
            let p = inst make_port();
            (inst consumer(p), inst consumer(p))
        }
    "
}

#[test]
fn reading_from_a_port_does_not_consume_it() {
    let code = "
        mod std { mod ports {
            entity read_port<T>(p: &mut T) -> T __builtin__
        }}

        entity make_port() -> &mut bool __builtin__
        entity consumer(x: &mut bool) -> bool __builtin__

        use std::ports::read_port;

        entity test() -> (bool, bool) {
            let p = inst make_port();
            let _ = inst consumer(p);
            (inst read_port(p), inst read_port(p))
        }
    ";
    build_items(code);
}

#[test]
fn set_statement_consumes_port() {
    let code = "
        entity e(p: &mut bool) -> bool {
            set p = false;
            false
        }";

    build_items(code);
}
