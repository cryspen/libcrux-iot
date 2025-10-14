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
#[cfg(any(eurydice, not(feature = "check-secret-independence")))]
/// wrapper for integer conversion
macro_rules! as_u64 {
    ($v:expr) => {
        $v as u64
    };
}

#[macro_export]
#[cfg(any(eurydice, not(feature = "check-secret-independence")))]
/// wrapper for integer conversion
macro_rules! as_u32 {
    ($v:expr) => {
        $v as u32
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

#[macro_export]
#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
/// wrapper for declassification
macro_rules! as_u64 {
    ($v:expr) => {{
        use libcrux_secrets::CastOps;
        $v.as_u64()
    }};
}

#[macro_export]
#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
/// wrapper for declassification
macro_rules! as_u32 {
    ($v:expr) => {{
        use libcrux_secrets::CastOps;
        $v.as_u32()
    }};
}

pub(crate) use as_u32;
pub(crate) use as_u64;
pub(crate) use classify;

#[cfg(all(not(eurydice), feature = "check-secret-independence"))]
pub(crate) use declassify;
