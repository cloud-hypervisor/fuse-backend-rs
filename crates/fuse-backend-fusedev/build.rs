fn main() {
    if std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default() == "macos" {
        println!("cargo:rustc-link-lib=framework=DiskArbitration");
        // The macFUSE session declares the CoreFoundation functions it needs
        // locally (macos_session.rs), so link the framework here — this used
        // to come in through the core-foundation-sys crate.
        println!("cargo:rustc-link-lib=framework=CoreFoundation");
    }
}
