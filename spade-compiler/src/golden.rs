#[cfg(test)]
use goldentests::{TestConfig, TestResult};

#[ignore]
#[test]
fn run_golden_tests() -> TestResult<()> {
    let config = TestConfig::new("../target/debug/spade", "goldentests", "// ")?;
    config.run_tests()
}
