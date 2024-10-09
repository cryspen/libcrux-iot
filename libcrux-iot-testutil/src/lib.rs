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
pub use logger::EventLogger;

extern crate alloc;

use alloc::{
    fmt::{Debug, Display},
    string::{String, ToString},
    vec,
    vec::Vec,
};

/// A test function.
pub type TestFn<L, E> = fn(l: &mut L) -> Result<(), E>;

#[derive(Debug)]
/// A test case. The name is used for filtering which tests to run.
pub struct TestCase<'a, L, E> {
    name: &'a str,
    test_fn: TestFn<L, E>,
}

impl<'a, L, E> TestCase<'a, L, E> {
    pub fn new(name: &'a str, test_fn: TestFn<L, E>) -> Self {
        Self { name, test_fn }
    }
}

#[derive(Default)]
/// A test suite containing all the tests that can be run
pub struct TestSuite<'a, L, E>(Vec<TestCase<'a, L, E>>);

impl<'a, L, E: Debug> TestSuite<'a, L, E> {
    /// Registers a new test in the test suite.
    pub fn register(&mut self, name: &'a str, test_fn: TestFn<L, E>) {
        self.0.push(TestCase { name, test_fn })
    }
}

#[derive(Debug)]
/// The test config contains information on the system and settings that control
/// how the tests are run.
pub struct TestConfig<'a> {
    pub core_freq: u32,
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
    pub fn parse_config(core_freq: u32, config: &'a str) -> Self {
        let mut early_abort = false;
        let mut only_names = vec![];

        for word in config.split_ascii_whitespace() {
            if word == "--early-abort" {
                early_abort = true
            } else {
                only_names.push(word)
            }
        }

        Self {
            core_freq,
            only_names,
            early_abort,
        }
    }

    /// Runs the test suite using the given logger. If `early_abort` is set, it
    /// returns the first error, wrapped in [`ErrorReport::EarlyAbort`].
    /// Otherwise it runs all tests and, if errors were encountered, returns the
    /// vector of all errors wrapped in [`ErrorReport::Combined`].
    pub fn run_test_suite<E, L: EventLogger>(
        &self,
        logger: &mut L,
        test_suite: TestSuite<L, E>,
    ) -> Result<(), ErrorReport<E>>
    where
        E: Display,
    {
        logger.log_event(TestUtilEvent::Launch(LaunchEvent {
            core_freq: self.core_freq,
        }));

        let mut errors = vec![];

        for test_case in test_suite.0 {
            if let Err(err) = self.run_test_case(logger, test_case) {
                if self.early_abort {
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

    /// If the configuration permits, runs the test case. Logs the appropriate
    /// messages, and returns the error returned by the test.
    pub fn run_test_case<E: Display, L: EventLogger>(
        &self,
        logger: &mut L,
        test_case: TestCase<L, E>,
    ) -> Result<(), E> {
        let all_tests_should_run = self.only_names.is_empty();
        let test_is_selected = self.only_names.contains(&test_case.name);
        let test_should_run = all_tests_should_run || test_is_selected;

        if !test_should_run {
            logger.log_event(TestUtilEvent::Test(TestEvent::Skip {
                test_name: String::from(test_case.name),
            }));

            return Ok(());
        }
        logger.log_event(TestUtilEvent::Test(TestEvent::Run {
            test_name: String::from(test_case.name),
        }));

        let result = (test_case.test_fn)(logger);

        match &result {
            Ok(_) => logger.log_event(TestUtilEvent::Test(TestEvent::Pass {
                test_name: String::from(test_case.name),
            })),
            Err(err) => {
                logger.log_event(TestUtilEvent::Test(TestEvent::Error {
                    test_name: String::from(test_case.name),
                    error_message: err.to_string(),
                }));
            }
        }

        result
    }
}
