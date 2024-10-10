//! This crate provides a small custom test runner in a binary. The test results
//! are streamed to a user provided logger. The goal here is to be able to easily
//! run tests and benchmarks on microcontrollers, where we don't have the
//! standard rust test runner available.
//!
//! The crate will support both tests and benchmarks, but so far only tests are
//! implemented.
//!
//! The core types in this crate are the [`TestConfig`] and the [`TestSuite`].
//! The test config contains information on the system and configures how the
//! tests are run. The test suite contains all the tests that can be run.
//!
//! A [`TestSuite`] can be created using `TestSuite::default()`, and new tests
//! can be added to it by calling [`TestSuite::register`].
//!
//! A [`TestConfig`] can be created using the [`TestConfig::parse_config`] function.
//! The config string is expected to be a whitespace-separated list of either
//! test names or the string `--early-abort`. If the string does not contain
//! any test names, all tests will be run. If it contains the string
//! `--early-abort`, the test runner will immediately abort execution when a test
//! returns an error.
//!
//! Test functions are represented by the [`TestFn`] type alias. Note that all
//! test functions in a test suite must return the same error, and that the
//! error must implement [`alloc::fmt::Display`].
//!
//! Note: Tests names should also be valid Rust identifiers. Most importantly,
//! they should not contain comma (`,`) characters, because these are used as
//! delimiters in the string encoding format.
#![no_std]

mod events;
mod logger;

pub use events::*;
pub use logger::vec_logger::VecLogger;
pub use logger::defmt_logger::DefmtInfoLogger;
pub use logger::EventLogger;

extern crate alloc;

use alloc::{
    fmt::{Debug, Display},
    string::{String, ToString},
    vec,
    vec::Vec,
};

/// A test function.
pub type TestFn<L, E, S> = fn(l: &mut L, state: &S) -> Result<(), E>;

#[derive(Debug)]
/// A test case. The name is used for filtering which tests to run.
pub struct TestCase<'a, L, E, S> {
    name: &'a str,
    test_fn: TestFn<L, E, S>,
}

impl<'a, L, E, S> TestCase<'a, L, E, S> {
    pub fn new(name: &'a str, test_fn: TestFn<L, E, S>) -> Self {
        Self { name, test_fn }
    }
}
impl<'a, L, E, S> TestCase<'a, L, E, S>
where
    L: EventLogger,
    E: Display,
{
    pub fn is_skipped(&self, config: &TestConfig) -> bool {
        let all_tests_should_run = config.only_names.is_empty();
        let test_is_selected = config.only_names.contains(&self.name);

        !all_tests_should_run && !test_is_selected
    }
    /// If the configuration permits, runs the test case. Logs the appropriate
    /// messages, and returns the error returned by the test.
    pub fn run(&self, logger: &mut L, state: &S) -> Result<(), E> {
        logger.log_event(TestUtilEvent::Test(TestEvent::Run {
            name: String::from(self.name),
        }));

        let result = (self.test_fn)(logger, state);

        match &result {
            Ok(_) => logger.log_event(TestUtilEvent::Test(TestEvent::Pass {
                name: String::from(self.name),
            })),
            Err(err) => {
                logger.log_event(TestUtilEvent::Test(TestEvent::Error {
                    name: String::from(self.name),
                    error_message: err.to_string(),
                }));
            }
        }

        result
    }

    /// If the configuration permits, runs the test case as a benchmark. Logs the
    /// appropriate messages, and returns the error returned by the test.
    pub fn benchmark(&self, logger: &mut L, run_id: u32, state: &S) -> Result<u32, E> {
        logger.log_event(TestUtilEvent::Benchmark(BenchmarkEvent::Run {
            name: String::from(self.name),
            run_id,
        }));

        let cycles_start = cortex_m::peripheral::DWT::cycle_count();
        let result = core::hint::black_box((self.test_fn)(logger, state));
        let cycles_end = cortex_m::peripheral::DWT::cycle_count();
        let cycles = cycles_end - cycles_start;

        match &result {
            Ok(_) => logger.log_event(TestUtilEvent::Benchmark(BenchmarkEvent::Done {
                name: String::from(self.name),
                run_id,
                cycles,
            })),
            Err(err) => {
                logger.log_event(TestUtilEvent::Benchmark(BenchmarkEvent::Error {
                    name: String::from(self.name),
                    run_id,
                    error_message: err.to_string(),
                }));
            }
        }

        result.map(|_| cycles)
    }
}

#[derive(Default)]
/// A test suite containing all the tests that can be run
pub struct TestSuite<'a, L, E, S>(Vec<TestCase<'a, L, E, S>>);

impl<'a, L, E: Debug, S> TestSuite<'a, L, E, S> {
    pub fn new() -> Self {
        Self (
            Vec::new()
        )
    }
    /// Registers a new test in the test suite.
    pub fn register(&mut self, name: &'a str, test_fn: TestFn<L, E, S>) {
        self.0.push(TestCase { name, test_fn })
    }
}

impl<'a, L: EventLogger, E: Display, S> TestSuite<'a, L, E, S> {
    /// Runs the test suite using the given logger. If `early_abort` is set, it
    /// returns the first error, wrapped in [`ErrorReport::EarlyAbort`].
    /// Otherwise it runs all tests and, if errors were encountered, returns the
    /// vector of all errors wrapped in [`ErrorReport::Combined`].
    pub fn run(&self, logger: &mut L, config: &TestConfig<'a>, state: &S) -> Result<(), ErrorReport<E>>
    where
        E: Display,
    {
        logger.log_event(TestUtilEvent::Launch(LaunchEvent {
            core_freq: config.core_freq,
        }));

        let mut errors = vec![];

        for test_case in &self.0 {
            if test_case.is_skipped(config) {
                logger.log_event(TestUtilEvent::Test(TestEvent::Skip {
                    name: String::from(test_case.name),
                }));

                continue;
            }

            if let Err(err) = test_case.run(logger, state) {
                if config.early_abort {
                    return Err(ErrorReport::EarlyAbort(err));
                } else {
                    errors.push(err)
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(ErrorReport::Combined(errors))
        }
    }

    /// Benchmarks the test suite using the given logger. If `early_abort` is
    /// set, it returns the first error, wrapped in [`ErrorReport::EarlyAbort`].
    /// Otherwise it runs all tests and, if errors were encountered, returns the
    /// vector of all errors wrapped in [`ErrorReport::Combined`].
    pub fn benchmark(
        &self,
        logger: &mut L,
        config: &TestConfig<'a>,
        state: &S
    ) -> Result<Vec<(&'a str, u32, u32)>, ErrorReport<E>>
    where
        E: Display + Debug,
    {
        logger.log_event(TestUtilEvent::Launch(LaunchEvent {
            core_freq: config.core_freq,
        }));

        let mut cycle_infos = vec![];
        let mut errors = vec![];

        for test_case in &self.0 {
            if test_case.is_skipped(config) {
                logger.log_event(TestUtilEvent::Test(TestEvent::Skip {
                    name: String::from(test_case.name),
                }));

                continue;
            }

            for run_id in 0..config.benchmark_runs {
                let result = test_case.benchmark(logger, run_id, state);

                if config.early_abort {
                    cycle_infos.push((
                        test_case.name,
                        run_id,
                        result.map_err(ErrorReport::EarlyAbort)?,
                    ));
                } else {
                    match result {
                        Ok(cycles) => cycle_infos.push((test_case.name, run_id, cycles)),
                        Err(err) => errors.push(err),
                    }
                }
            }
        }

        if errors.is_empty() {
            Ok(cycle_infos)
        } else {
            Err(ErrorReport::Combined(errors))
        }
    }
}

#[derive(Debug)]
/// The test config contains information on the system and settings that control
/// how the tests are run.
pub struct TestConfig<'a> {
    pub core_freq: u32,
    pub benchmark_runs: u32,
    pub only_names: Vec<&'a str>,
    pub early_abort: bool,
}

#[derive(Debug, PartialEq, Eq)]
/// In case of early aborts, just a single error is returned. If not, the errors
/// are collected in a `Vec` and returned as the `Combined` variant.
pub enum ErrorReport<E> {
    EarlyAbort(E),
    Combined(Vec<E>),
}

impl<E: Display> Display for ErrorReport<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ErrorReport::EarlyAbort(err) => err.fmt(f),
            ErrorReport::Combined(errs) => {
                writeln!(f, "encountered multimple errors:")?;
                for err in errs {
                    writeln!(f, "- {err}")?
                }
                Ok(())
            }
        }
    }
}

impl<'a> TestConfig<'a> {
    /// Parses a config string.
    pub fn parse_config(core_freq: u32, config: &'a str) -> Result<Self, String> {
        let mut early_abort = false;
        let mut only_names = vec![];
        let mut benchmark_runs = 5;

        for word in config.split_ascii_whitespace() {
            if word.starts_with("--") {
                // decompose key-value flags
                let (word, value) = if let Some((name, value)) = word.split_once("=") {
                    (name, Some(value))
                } else {
                    (word, None)
                };

                // handle the flags
                match (word, value) {
                    ("--early-abord", _) => early_abort = true,
                    ("--benchmark-runs", Some(value)) => {
                        benchmark_runs = value.parse().map_err(|err| {
                            alloc::format!("error parsing --benchmark-runs: {err}")
                        })?;
                    }
                    ("--benchmark-runs", None) => {
                        return Err("--benchmark-runs needs a value".to_string())
                    }
                    _ => {
                        return Err(alloc::format!("unknown flag: {word}"));
                    }
                }
            } else {
                only_names.push(word)
            }
        }

        Ok(Self {
            core_freq,
            only_names,
            early_abort,
            benchmark_runs,
        })
    }
}
