test_mir_to_fil:
	cargo build --manifest-path spade-compiler/Cargo.toml
	./target/debug/spade test.sp -o test.fil
