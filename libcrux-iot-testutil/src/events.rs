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
    Run { name: String },
    /// This is emitted if the runner encounters a test that should be skipped
    Skip { name: String },
    /// This is emitted if the test ran successfully
    Pass { name: String },
    /// This is emitted if the test failed
    Error { name: String, error_message: String },
}

/// These are events related to benchmarks
#[derive(Debug, PartialEq, Eq)]
pub enum BenchmarkEvent {
    /// This is emitted when an iteration of a benchmark is started
    Run { name: String, run_id: u32 },
    /// This is emitted if the runner encounters a test that should be skipped
    Skip { name: String },
    /// This is emitted when an iteration of a benchmark is finished
    Done {
        name: String,
        run_id: u32,
        cycles: u32,
    },
    /// This is emitted when an iteration of a benchmark returned an error
    Error {
        name: String,
        run_id: u32,
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
            TestEvent::Run { name: test_name } => ('r', test_name, None),
            TestEvent::Skip { name: test_name } => ('s', test_name, None),
            TestEvent::Pass { name: test_name } => ('p', test_name, None),

            TestEvent::Error {
                name: test_name,
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
                name: rest.to_string(),
            }),
            "s" => Some(Self::Skip {
                name: rest.to_string(),
            }),
            "p" => Some(Self::Pass {
                name: rest.to_string(),
            }),
            "e" => {
                let (test_name, error_message) = rest.split_once(',')?;

                Some(Self::Error {
                    name: test_name.to_string(),
                    error_message: error_message.to_string(),
                })
            }
            _ => None,
        }
    }
}

impl BenchmarkEvent {
    pub fn encode(&self, dest: &mut String) {
        let (tag, name, run_id) = match self {
            BenchmarkEvent::Run { name, run_id } => ('r', name, Some(run_id)),
            BenchmarkEvent::Skip { name } => ('s', name, None),
            BenchmarkEvent::Done { name, run_id, .. } => ('d', name, Some(run_id)),
            BenchmarkEvent::Error { name, run_id, .. } => ('e', name, Some(run_id)),
        };

        dest.push(tag);
        dest.push(',');
        dest.push_str(name);
        if let Some(run_id) = run_id {
            dest.push(',');
            dest.push_str(&run_id.to_string());
        }

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
        let (run_id, rest) = rest.split_once(',')?;
        let run_id = run_id.parse().ok()?;
        match tag {
            "r" => Some(Self::Run {
                name: rest.to_string(),
                run_id,
            }),
            "p" => {
                let (benchmark_name, cycles) = rest.split_once(',')?;

                Some(Self::Done {
                    name: benchmark_name.to_string(),
                    run_id,
                    cycles: cycles.parse().ok()?,
                })
            }
            "e" => {
                let (benchmark_name, error_message) = rest.split_once(',')?;

                Some(Self::Error {
                    name: benchmark_name.to_string(),
                    run_id,
                    error_message: error_message.to_string(),
                })
            }
            _ => None,
        }
    }
}
