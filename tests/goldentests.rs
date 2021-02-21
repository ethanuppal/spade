use goldentests::{TestConfig, TestResult};

#[test]
fn run_golden_tests() -> TestResult<()> {
    let config = TestConfig::new("target/debug/spade", "goldentests", "// ")?;
    config.run_tests()
}
