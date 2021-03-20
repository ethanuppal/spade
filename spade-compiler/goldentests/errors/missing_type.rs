entity missing_type(a: int<8>) -> {
    a
}

// args: -o /dev/null --no-color
// expected exit status: 1
// expected stderr:
// error: Unexpected token. Got `{`, expected type
//   ┌─ goldentests/errors/missing_type.rs:1:35
//   │
// 1 │ entity missing_type(a: int<8>) -> {
//   │                                   ^ Expected a type
// 
// Error: aborting due to previous error
