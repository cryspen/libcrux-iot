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

#[macro_export]
#[cfg(any(eurydice, not(feature = "check-secret-independence")))]
/// wrapper for declassification
macro_rules! declassify {
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

#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
/// wrapper for declassification
macro_rules! declassify {
    ($v:expr) => {{
        use libcrux_secrets::Declassify;
        thing.declassify()
    }};
}

pub(crate) use classify;
pub(crate) use classify_ref;
pub(crate) use declassify;
