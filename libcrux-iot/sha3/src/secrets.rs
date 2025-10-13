#[macro_export]
#[cfg(any(eurydice, not(feature = "check-secret-independence")))]
/// wrapper for classification
macro_rules! classify {
    ($v:expr) => {
        $v
    };
}

#[macro_export]
#[cfg(any(eurydice, not(feature = "check-secret-independence")))]
/// wrapper for reference classification
macro_rules! classify_ref {
    ($v:expr) => {
        $v
    };
}

#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
/// wrapper for classification
macro_rules! classify {
    ($v:expr) => {{
        use libcrux_secrets::Classify;
        thing.classify()
    }};
}

#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
/// wrapper for reference classification
macro_rules! classify_ref {
    ($v:expr) => {{
        use libcrux_secrets::ClassifyRef;
        thing.classify_ref()
    }};
}

pub(crate) use classify;
// So far classify_ref is only used in lib.rs, where it is in scope by default due to the way
// macro_export works. That is why we don't export it here.
