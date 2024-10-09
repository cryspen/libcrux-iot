use libcrux_iot_testutil::VecLogger;
use libcrux_iot_testutil::*;

#[test]
fn run_tests_no_early_abort() {
    fn test_pass<L: EventLogger>(_l: &mut L) -> Result<(), String> {
        Ok(())
    }

    fn test_log<L: EventLogger>(l: &mut L) -> Result<(), String> {
        l.log_user("this is a test log");
        Ok(())
    }

    fn test_error<L: EventLogger>(_l: &mut L) -> Result<(), String> {
        Err("an error occurred!".to_string())
    }

    fn test_skip<L: EventLogger>(_l: &mut L) -> Result<(), String> {
        unreachable!()
    }

    let mut test_suite = TestSuite::default();
    test_suite.register("test_pass", test_pass);
    test_suite.register("test_log", test_log);
    test_suite.register("test_error", test_error);
    test_suite.register("test_skip", test_skip);

    let test_config = TestConfig {
        core_freq: 25_000_000,
        only_names: vec!["test_pass", "test_log", "test_error"],
        early_abort: false,
        benchmark_runs: 5,
    };

    let mut logger = VecLogger::default();

    let err = test_suite
        .run(&mut logger, &test_config)
        .expect_err("expected test suite failure");

    assert_eq!(
        err,
        ErrorReport::Combined(vec!["an error occurred!".to_string()])
    );

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
