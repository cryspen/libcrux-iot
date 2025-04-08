use std::{env, path::Path};

#[cfg(not(windows))]
fn create_bindings(home_dir: &Path) {
    let mlkem_dir = home_dir.join("pqm4/crypto_kem/ml-kem-1024/m4fspeed/api.h");
    let fips202_dir = home_dir.join("pqm4/mupq/common/fips202.h");
    let clang_args = vec![format!("-I{}", mlkem_dir.display()), format!("-I{}", fips202_dir.display())];

    let bindings = bindgen::Builder::default()
        // Header to wrap headers
        .header("wrapper.h")
        // Set include paths for headers
        .clang_args(clang_args)
        // Generate bindings
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .use_core()
        .generate()
        .expect("Unable to generate bindings");

    let home_bindings = home_dir.join("src/bindings.rs");
    bindings
        .write_to_file(home_bindings)
        .expect("Couldn't write bindings!");
}

#[cfg(windows)]
fn create_bindings(_: &Path) {}

// This triggers the mupq build system.
fn build() {
    if !std::process::Command::new("git")
        .arg("submodule")
        .arg("update")
        .arg("--init")
        .arg("--recursive")
        .status()
        .expect("could not run git")
        .success()
    {
        panic!("git could not update submodules.")
    }
    
    if !std::process::Command::new("make")
        .arg("-C")
        .arg("pqm4")
        .arg("clean")
        .env("PLATFORM", "nucleo-l4r5zi")
        .status()
        .expect("could not run make")
        .success()
    {
        panic!("Could not run `make clean` before building shared libraries.")
    }

    // `make clean` might delete the target directory, so we have to create it
    let lib_path = Path::new("pqm4/obj");

    std::fs::create_dir(lib_path).unwrap();

    
    let lib_path = lib_path.canonicalize().unwrap_or_else(|_| panic!("Could not canonicalize {lib_path:?}"));
    
    // Tell cargo to look for shared libraries in the specified directory
    println!("cargo:rustc-link-search={}", lib_path.to_str().unwrap());

    // Tell cargo to tell rustc to link our `hello` library. Cargo will
    // automatically know it must look for a `libhello.a` file.
    println!("cargo:rustc-link-lib=crypto_kem_ml-kem-1024_m4fspeed");
    println!("cargo:rustc-link-lib=symcrypto");

    if !std::process::Command::new("make")
        .arg("-C")
        .arg("pqm4")
        .arg("obj/libcrypto_kem_ml-kem-1024_m4fspeed.a")
        .env("PLATFORM", "nucleo-l4r5zi")
        .status()
        .expect("could not run make")
        .success()
    {
        panic!("Could not build ML-KEM library")
    }

    if !std::process::Command::new("make")
        .arg("-C")
        .arg("pqm4")
        .arg("obj/libsymcrypto.a")
        .env("PLATFORM", "nucleo-l4r5zi")
        .status()
        .expect("could not run make")
        .success()
    {
        panic!("Could not build host crypto library")
    }
}

pub fn main() {
    // Get ENV variables
    let home_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let home_path = Path::new(&home_dir);

    // Build the C/ASM files
    build();

    // Set re-run trigger for all of s
    println!("cargo:rerun-if-changed=pqm4");

    // Generate new bindings. This is a no-op on Windows.
    create_bindings(home_path);
}
