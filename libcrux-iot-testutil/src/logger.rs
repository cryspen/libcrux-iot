use alloc::string::ToString;

use super::TestUtilEvent;

/// Provides the test runners an interface where they can emit events to the host.
pub trait EventLogger {
    /// Logs an event
    fn log_event(&mut self, ev: TestUtilEvent);

    /// Logs a user event.
    /// Ideally we could just use defmt as before, but if we use the defmt-backed logger, our
    /// custom logs will share the channel with the events. In order to work around that, we added
    /// a custom event type that just contains a user-chosen string.
    ///
    /// This sort of makes the whole point of defmt a bit moot, so we might want to find a better
    /// solution for this. Another approach would be to use a different defmt-level, or to prefix
    /// the messages in defmt by "u,", because that is the domain separation we use for user logs
    /// in our encoding.
    fn log_user(&mut self, text: impl ToString) {
        self.log_event(TestUtilEvent::User(text.to_string()))
    }
}

pub mod vec_logger {
    use alloc::vec::Vec;

    use super::*;

    #[derive(Default)]
    /// A logger that writes all events to a Vec.
    pub struct VecLogger(Vec<TestUtilEvent>);

    impl EventLogger for VecLogger {
        fn log_event(&mut self, ev: TestUtilEvent) {
            self.0.push(ev)
        }
    }

    impl VecLogger {
        pub fn into_events(self) -> Vec<TestUtilEvent> {
            self.0
        }
    }
}

pub mod defmt_logger {
    use super::*;
    use alloc::string::String;

    // A logger that encodes and writes all events using `defmt::info!`.
    pub struct DefmtInfoLogger;

    impl EventLogger for DefmtInfoLogger {
        fn log_event(&mut self, ev: TestUtilEvent) {
            let mut encoded = String::with_capacity(64);
            ev.encode(&mut encoded);
            defmt::info!("{}", encoded);
        }
    }
}
