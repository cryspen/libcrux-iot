use libcrux_iot_testutil::VecLogger;
use libcrux_iot_testutil::*;

extern crate alloc;

#[derive(Debug, PartialEq, Eq)]
struct TestError;

impl alloc::fmt::Display for TestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "an error occurred!")
    }
}

#[test]
fn run_tests_no_early_abort() {
    fn test_pass<L: EventLogger>(_logger: &mut L, _state: &()) -> Result<(), TestError> {
        Ok(())
    }

    fn test_log<L: EventLogger>(logger: &mut L, _state: &()) -> Result<(), TestError> {
        logger.log_user("this is a test log");
        Ok(())
    }

    fn test_error<L: EventLogger>(_logger: &mut L, _state: &()) -> Result<(), TestError> {
        return Err(TestError);
        //Err(.to_string())
    }

    fn test_skip<L: EventLogger>(_logger: &mut L, _state: &()) -> Result<(), TestError> {
        unreachable!()
    }

    let cases = [
        TestCase::new("test_pass", test_pass),
        TestCase::new("test_log", test_log),
        TestCase::new("test_error", test_error),
        TestCase::new("test_pass", test_pass),
    ];

    let test_suite = TestSuite::new(&cases);

    let test_config = TestConfig {
        core_freq: 25_000_000,
        only_names: vec!["test_pass", "test_log", "test_error"],
        early_abort: false,
        benchmark_runs: 5,
    };

    let mut logger = VecLogger::default();

    let err = test_suite
        .run(&mut logger, &test_config, &())
        .expect_err("expected test suite failure");

    assert_eq!(err, ErrorReport::Combined(vec![TestError]));

    let events = logger.into_events();

    assert_eq!(
        events[0],
        TestUtilEvent::Launch(LaunchEvent {
            core_freq: 25_000_000
        })
    );
    assert_eq!(
        events[1],
        TestUtilEvent::Test(TestEvent::Run {
            name: "test_pass".to_string()
        })
    );
    assert_eq!(
        events[2],
        TestUtilEvent::Test(TestEvent::Pass {
            name: "test_pass".to_string()
        })
    );
    assert_eq!(
        events[3],
        TestUtilEvent::Test(TestEvent::Run {
            name: "test_log".to_string()
        })
    );
    assert_eq!(
        events[4],
        TestUtilEvent::User("this is a test log".to_string())
    );
    assert_eq!(
        events[5],
        TestUtilEvent::Test(TestEvent::Pass {
            name: "test_log".to_string()
        })
    );
    assert_eq!(
        events[6],
        TestUtilEvent::Test(TestEvent::Run {
            name: "test_error".to_string()
        })
    );
    assert_eq!(
        events[7],
        TestUtilEvent::Test(TestEvent::Error {
            name: "test_error".to_string(),
            error_message: "an error occurred!".to_string()
        })
    );
    assert_eq!(
        events[8],
        TestUtilEvent::Test(TestEvent::Skip {
            name: "test_skip".to_string()
        })
    );
}
