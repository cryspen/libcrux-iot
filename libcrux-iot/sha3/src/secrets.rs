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

#[macro_export]
#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
/// wrapper for classification
macro_rules! classify {
    ($v:expr) => {{
        use libcrux_secrets::Classify;
        $v.classify()
    }};
}

#[macro_export]
#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
/// wrapper for reference classification
macro_rules! classify_ref {
    ($v:expr) => {{
        use libcrux_secrets::ClassifyRef;
        $v.classify_ref()
    }};
}

#[macro_export]
#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
/// wrapper for declassification
macro_rules! declassify {
    ($v:expr) => {{
        use libcrux_secrets::Declassify;
        $v.declassify()
    }};
}

pub(crate) use classify;

#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
pub(crate) use declassify;
