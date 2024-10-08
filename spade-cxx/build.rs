fn main() {
    // This will consider the ffi part in lib.rs in order to
    // generate lib.rs.h and lib.rs.cc
    // minimal example: no C++ code to be called from Rust
    cxx_build::bridge("src/spade.rs")
        .flag_if_supported("-std=c++11")
        .compile("spade-cxx");

    println!("cargo:rerun-if-changed=src/spade.rs");
}
