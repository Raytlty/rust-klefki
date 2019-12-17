// Copyright © 2016–2019 University of Malta

// Copying and distribution of this file, with or without
// modification, are permitted in any medium without royalty provided
// the copyright notice and this notice are preserved. This file is
// offered as-is, without any warranty.

use std::{
    env,
    ffi::OsString,
    fs::{self, File},
    io::{Result as IoResult, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

struct Environment {
    out_dir: PathBuf,
    rustc: OsString,
}

fn main() {
    let env = Environment {
        out_dir: PathBuf::from(cargo_env("OUT_DIR")),
        rustc: cargo_env("RUSTC"),
    };
    env.check_feature("try_from", TRY_TRY_FROM, Some("try_from"));
    env.check_feature("maybe_uninit", TRY_MAYBE_UNINIT, Some("maybe_uninit"));
    env.check_ffi_panic_aborts();
    if env::var_os("CARGO_FEATURE_GMP_MPFR_SYS").is_some() {
        let bits =
            env::var_os("DEP_GMP_LIMB_BITS").expect("DEP_GMP_LIMB_BITS not set by gmp-mfpr-sys");
        let bits = bits
            .to_str()
            .expect("DEP_GMP_LIMB_BITS contains unexpected characters");
        if bits != "32" && bits != "64" {
            panic!("Limb bits not 32 or 64: \"{}\"", bits);
        }
        println!("cargo:rustc-cfg=gmp_limb_bits_{}", bits);
    }
}

impl Environment {
    fn check_feature(&self, name: &str, contents: &str, nightly_features: Option<&str>) {
        let try_dir = self.out_dir.join(format!("try_{}", name));
        let filename = format!("try_{}.rs", name);
        create_dir_or_panic(&try_dir);
        println!("$ cd {:?}", try_dir);

        enum Iteration {
            Stable,
            Unstable,
        }
        for i in &[Iteration::Stable, Iteration::Unstable] {
            let s;
            let file_contents = match *i {
                Iteration::Stable => contents,
                Iteration::Unstable => match nightly_features {
                    Some(features) => {
                        s = format!("#![feature({})]\n{}", features, contents);
                        &s
                    }
                    None => continue,
                },
            };
            create_file_or_panic(&try_dir.join(&filename), file_contents);
            let mut cmd = Command::new(&self.rustc);
            cmd.current_dir(&try_dir)
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .args(&[&filename, "--emit=dep-info,metadata"]);
            println!("$ {:?} >& /dev/null", cmd);
            let status = cmd
                .status()
                .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
            if status.success() {
                println!("cargo:rustc-cfg={}", name);
                if let Iteration::Unstable = *i {
                    println!("cargo:rustc-cfg=nightly_{}", name);
                }
                break;
            }
        }

        remove_dir_or_panic(&try_dir);
    }

    fn check_ffi_panic_aborts(&self) {
        let ident = "ffi_panic_aborts";
        // try two different codes to make sure code is set by us
        let codes = &[1, 2];
        let try_dir = self.out_dir.join(format!("try_{}", ident));
        create_dir_or_panic(&try_dir);
        let mut panic_aborts = true;
        for code in codes {
            let contents = format!("{}\nconst CODE: i32 = {};\n", TRY_FFI_PANIC_ABORTS, code);
            let filename = format!("try_{}_{}.rs", ident, code);
            let out = format!("out_{}.exe", code);
            create_file_or_panic(&try_dir.join(&filename), &contents);
            let mut cmd = Command::new(&self.rustc);
            cmd.current_dir(&try_dir).args(&[&filename, "-o", &out]);
            println!("$ cd {:?}", try_dir);
            println!("$ {:?}", cmd);
            let status = cmd
                .status()
                .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
            assert!(status.success(), "Compiling failed: {:?}", cmd);
            cmd = Command::new(try_dir.join(&out));
            cmd.stdout(Stdio::null()).stderr(Stdio::null());
            println!("$ {:?} >& /dev/null", cmd);
            let status = cmd
                .status()
                .unwrap_or_else(|_| panic!("Unable to execute: {:?}", cmd));
            if status.code() != Some(*code) {
                panic_aborts = false;
                break;
            }
        }
        if panic_aborts {
            println!("cargo:rustc-cfg=ffi_panic_aborts");
        }
        // Do not panic if this directory cannot be removed, AppVeyor
        // fails trying for Windows.
        remove_dir(&try_dir)
            .unwrap_or_else(|_| println!("Unable to remove directory: {:?}", try_dir));
    }
}

fn cargo_env(name: &str) -> OsString {
    env::var_os(name)
        .unwrap_or_else(|| panic!("environment variable not found: {}, please use cargo", name))
}

fn remove_dir(dir: &Path) -> IoResult<()> {
    if !dir.exists() {
        return Ok(());
    }
    assert!(dir.is_dir(), "Not a directory: {:?}", dir);
    println!("$ rm -r {:?}", dir);
    fs::remove_dir_all(dir)
}

fn remove_dir_or_panic(dir: &Path) {
    remove_dir(dir).unwrap_or_else(|_| panic!("Unable to remove directory: {:?}", dir));
}

fn create_dir(dir: &Path) -> IoResult<()> {
    println!("$ mkdir -p {:?}", dir);
    fs::create_dir_all(dir)
}

fn create_dir_or_panic(dir: &Path) {
    create_dir(dir).unwrap_or_else(|_| panic!("Unable to create directory: {:?}", dir));
}

fn create_file_or_panic(filename: &Path, contents: &str) {
    println!("$ printf %s {:?}... > {:?}", &contents[0..20], filename);
    let mut file =
        File::create(filename).unwrap_or_else(|_| panic!("Unable to create file: {:?}", filename));
    file.write_all(contents.as_bytes())
        .unwrap_or_else(|_| panic!("Unable to write to file: {:?}", filename));
}

const TRY_TRY_FROM: &str = r#"// try_try_from.rs
use std::convert::TryFrom;
fn main() {
    let _ = i8::try_from(1u64);
}
"#;

const TRY_MAYBE_UNINIT: &str = r#"// try_maybe_uninit.rs
use std::mem::MaybeUninit;
fn main() {
    let mut x = MaybeUninit::<u8>::zeroed();
    let _ = x.as_ptr();
    let _ = x.as_mut_ptr();
    let _ = unsafe { x.assume_init() };
    let _ = MaybeUninit::<u8>::uninit();
}
"#;

const TRY_FFI_PANIC_ABORTS: &str = r#"// try_ffi_panic_aborts.rs
extern "C" fn ffi_panic() {
    panic!();
}

type Handler = Option<unsafe extern "C" fn(i: i32)>;
extern "C" {
    pub fn signal(signum: i32, handler: Handler) -> Handler;
}
extern "C" fn handler(_: i32) {
    std::process::exit(CODE);
}

fn main() {
    // catch some signals and exit(CODE) instead
    unsafe {
        // SIGILL
        signal(4, Some(handler));
        // unix SIGABRT
        signal(6, Some(handler));
        // windows SIGABRT
        signal(22, Some(handler));
    }
    let _ = std::panic::catch_unwind(|| ffi_panic());
}
"#;
