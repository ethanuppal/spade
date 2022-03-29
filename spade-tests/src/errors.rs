use codespan_reporting::term::termcolor::Buffer;

use spade::Opt;

macro_rules! snapshot_error {
    ($fn:ident, $src:literal) => {
        #[test]
        fn $fn() {
            let source = unindent::unindent($src);
            let mut buffer = Buffer::no_color();
            let opts = Opt {
                error_buffer: &mut buffer,
                outfile: None,
                mir_output: None,
                print_type_traceback: false,
                print_parse_traceback: false,
            };

            let _ = spade::compile(vec![("testinput".to_string(), source.to_string())], opts);

            insta::assert_snapshot!(
                std::str::from_utf8(buffer.as_slice()).expect("error contains invalid utf-8")
            );
        }
    };
}

snapshot_error!(
    return_type_mismatch,
    "
    entity main() -> int<1> {
        let a: int<2> = 0;
        a
    }
    "
);
