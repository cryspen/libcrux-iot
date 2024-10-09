extern crate alloc;

use alloc::string::{String, ToString};

/// The top-level event
#[derive(Debug, PartialEq, Eq)]
pub enum TestUtilEvent {
    /// This is emitted once at the start of a test suite
    Launch(LaunchEvent),
    /// These are events related to tests
    Test(TestEvent),
    /// These are events related to benchmarks
    Benchmark(BenchmarkEvent),
    /// These are user-generated events, most likely for logging
    User(String),
}

/// This is emitted once at the start of a test suite
#[derive(Debug, PartialEq, Eq)]
pub struct LaunchEvent {
    /// The frequency of the CPU core.
    pub core_freq: u32,
}

/// These are events related to tests
#[derive(Debug, PartialEq, Eq)]
pub enum TestEvent {
    /// This is emitted right before a test is run
    Run { test_name: String },
    /// This is emitted if the runner encounters a test that should be skipped
    Skip { test_name: String },
    /// This is emitted if the test ran successfully
    Pass { test_name: String },
    /// This is emitted if the test failed
    Error {
        test_name: String,
        error_message: String,
    },
}

/// These are events related to benchmarks
#[derive(Debug, PartialEq, Eq)]
pub enum BenchmarkEvent {
    Run {
        benchmark_name: String,
    },
    Done {
        benchmark_name: String,
        cycles: u32,
    },
    Error {
        benchmark_name: String,
        error_message: String,
    },
}

impl TestUtilEvent {
    pub fn encode(&self, dest: &mut String) {
        match self {
            TestUtilEvent::Launch(ev) => {
                dest.push_str("l,");
                ev.encode(dest);
            }
            TestUtilEvent::Test(ev) => {
                dest.push_str("t,");
                ev.encode(dest);
            }
            TestUtilEvent::Benchmark(ev) => {
                dest.push_str("b,");
                ev.encode(dest);
            }
            TestUtilEvent::User(text) => {
                dest.push_str("u,");
                dest.push_str(text);
            }
        }
    }

    pub fn parse(data: &str) -> Option<Self> {
        let (tag, rest) = data.split_once(',')?;

        match tag {
            "l" => Some(Self::Launch(LaunchEvent::parse(rest)?)),
            "t" => Some(Self::Test(TestEvent::parse(rest)?)),
            "b" => Some(Self::Benchmark(BenchmarkEvent::parse(rest)?)),
            "u" => Some(Self::User(rest.to_string())),
            _ => None,
        }
    }
}

impl LaunchEvent {
    pub fn encode(&self, dest: &mut String) {
        // the schema version
        dest.push_str("0,");
        dest.push_str(&self.core_freq.to_string());
    }

    pub fn parse(data: &str) -> Option<Self> {
        let (schema_version, rest) = data.split_once(',')?;

        if schema_version != "0" {
            None
        } else {
            Some(Self {
                core_freq: rest.parse().ok()?,
            })
        }
    }
}

impl TestEvent {
    pub fn encode(&self, dest: &mut String) {
        let (tag, name, err_msg) = match self {
            TestEvent::Run { test_name } => ('r', test_name, None),
            TestEvent::Skip { test_name } => ('s', test_name, None),
            TestEvent::Pass { test_name } => ('p', test_name, None),

            TestEvent::Error {
                test_name,
                error_message,
            } => ('p', test_name, Some(error_message)),
        };

        dest.push(tag);
        dest.push(',');
        dest.push_str(name);
        if let Some(err_msg) = err_msg {
            dest.push(',');
            dest.push_str(err_msg)
        }
    }

    pub fn parse(data: &str) -> Option<Self> {
        let (tag, rest) = data.split_once(',')?;
        match tag {
            "r" => Some(Self::Run {
                test_name: rest.to_string(),
            }),
            "s" => Some(Self::Skip {
                test_name: rest.to_string(),
            }),
            "p" => Some(Self::Pass {
                test_name: rest.to_string(),
            }),
            "e" => {
                let (test_name, error_message) = rest.split_once(',')?;

                Some(Self::Error {
                    test_name: test_name.to_string(),
                    error_message: error_message.to_string(),
                })
            }
            _ => None,
        }
    }
}

impl BenchmarkEvent {
    pub fn encode(&self, dest: &mut String) {
        let (tag, name) = match self {
            BenchmarkEvent::Run { benchmark_name } => ('r', benchmark_name),
            BenchmarkEvent::Done { benchmark_name, .. } => ('d', benchmark_name),
            BenchmarkEvent::Error { benchmark_name, .. } => ('e', benchmark_name),
        };

        dest.push(tag);
        dest.push(',');
        dest.push_str(name);

        match self {
            BenchmarkEvent::Done { cycles, .. } => {
                dest.push(',');
                dest.push_str(&cycles.to_string())
            }
            BenchmarkEvent::Error { error_message, .. } => {
                dest.push(',');
                dest.push_str(error_message)
            }
            _ => {}
        }
    }

    pub fn parse(data: &str) -> Option<Self> {
        let (tag, rest) = data.split_once(',')?;
        match tag {
            "r" => Some(Self::Run {
                benchmark_name: rest.to_string(),
            }),
            "p" => {
                let (benchmark_name, cycles) = rest.split_once(',')?;

                Some(Self::Done {
                    benchmark_name: benchmark_name.to_string(),
                    cycles: cycles.parse().ok()?,
                })
            }
            "e" => {
                let (benchmark_name, error_message) = rest.split_once(',')?;

                Some(Self::Error {
                    benchmark_name: benchmark_name.to_string(),
                    error_message: error_message.to_string(),
                })
            }
            _ => None,
        }
    }
}
