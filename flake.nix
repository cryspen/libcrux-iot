#
#       Disclaimer: This nix environment is provided as-is.
#       None of this is officially supported and use is at your own risk.
#       We do not maintain or support nix environments.
#
{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
    # Keep this revision in sync with EURYDICE_REV in [libcrux/.docker/c/Dockerfile](https://github.com/cryspen/libcrux/blob/main/.docker/c/Dockerfile),
    # which is what CI uses for the extraction.
    eurydice.url = "github:aeneasverif/eurydice/aaa9fa657fb6f09802edb890252040d94cd93982";
    eurydice.inputs.karamel.inputs.fstar.follows = "fstar-pinned";
    hax.url = "github:hacspec/hax/87ba96831ecfeb7dbb54efcf97036fbc5f25bc71";
    fstar-pinned.url = "github:FStarLang/FStar/v2025.10.06";

    # --- Aeneas/Lean SHA-3 proof toolchain ---------------------------------
    # Used only by the `aeneas-lean` devShell. Keep these revisions in sync
    # with `libcrux-iot/sha3/proofs/aeneas-lean/{lean-toolchain,lakefile.toml}`
    # and `libcrux-iot/sha3/hax_aeneas.py`.
    #
    # `hax-evit` is the private fork the Lean extraction requires. It is fetched
    # over SSH, so the calling user needs read access (and an SSH key/agent
    # configured) for `nix develop .#aeneas-lean` to evaluate.
    hax-evit.url = "git+ssh://git@github.com/cryspen/hax-evit?ref=refs/heads/main&rev=1f85fc13b9967080cc657863e2000ba5d4aa8647";
    # cryspen/aeneas@nightly-2026.06.04 == 8d2077c (matches AENEAS_VERSION in
    # hax_aeneas.py). Its flake.lock pins the matching Charon nightly-2026.06.02,
    # and its default package bundles a `charon` binary alongside `aeneas`.
    aeneas.url = "github:cryspen/aeneas/nightly-2026.06.04";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      rust-overlay,
      eurydice,
      hax,
      fstar-pinned,
      aeneas,
      ...
    }@inputs:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };
        charon = eurydice.inputs.charon;
        fstar = fstar-pinned;
        karamel = eurydice.packages.${system}.karamel;

        tools-environment = {
          CHARON_HOME = charon.packages.${system}.charon;
          EURYDICE_HOME = pkgs.runCommand "eurydice-home" { } ''
            mkdir -p $out
            cp -r ${eurydice.packages.${system}.default}/bin/eurydice $out
            cp -r ${eurydice}/include $out
          '';
          FSTAR_HOME = fstar.packages.${system}.default;
          HAX_HOME = hax;
          KRML_HOME = karamel;

          CHARON_REV = charon.rev or "dirty";
          EURYDICE_REV = eurydice.rev or "dirty";
          KRML_REV = karamel.version;
          FSTAR_REV = fstar.rev or "dirty";
          LIBCRUX_REV = self.rev or "dirty";
        };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [
            "rust-src"
            "rust-analyzer"
            "llvm-tools-preview"
          ];
          # Targets needed for libcrux-nucleo-l4r5zi (real board + qemu mps2-an386).
          targets = [ "thumbv7em-none-eabihf" ];
        };

        # defmt-print decodes the rzCOBS-framed log stream that
        # libcrux-nucleo-l4r5zi emits over ARM semihosting under qemu.
        # Pinned to the 0.3.x line (defmt 0.3 compatible).
        defmt-print = pkgs.rustPlatform.buildRustPackage rec {
          pname = "defmt-print";
          version = "0.3.13";
          src = pkgs.fetchCrate {
            inherit pname version;
            hash = "sha256-j1qtHKZNMkPkAZg6Vw6bXqZjBBjkgRvLLuS8d3tJBGI=";
          };
          cargoHash = "sha256-BoDlig4uLMBcejI6AOjaoVOQ+DveTV9jn1Q3vC2bY74=";
          doCheck = false;
        };

        # --- Aeneas/Lean toolchain (used by devShells.aeneas-lean) ----------
        # `hax` and `aeneas` bake their version/commit into the binary at build
        # time (hax via `env!("HAX_GIT_COMMIT_HASH")`, aeneas via a dune rule
        # running `git describe`). Built from a Nix source tree (no `.git`),
        # both report "unknown", so the version checks in `hax_aeneas.py` fail.
        #
        # We wrap each binary so the version query reports the flake-locked rev
        # — the exact source Nix built — and pass every other invocation
        # straight through. The reported value is taken from the lock, so it
        # cannot drift from what is actually built.
        haxEvitPkg = inputs.hax-evit.packages.${system}.default;
        haxEvitRev = inputs.hax-evit.rev;
        # `cargo hax --version` (clap long-version) is what the script greps for
        # `commit=<rev>`; everything else passes through to the real binary.
        haxVersionScript = pkgs.writeShellScript "cargo-hax" ''
          case " $* " in
            *" --version "*)
              echo "hax"
              echo "commit=${haxEvitRev}"
              exit 0
              ;;
          esac
          exec ${haxEvitPkg}/bin/cargo-hax "$@"
        '';
        haxEvit = pkgs.symlinkJoin {
          name = "hax-evit-version-wrapped";
          paths = [ haxEvitPkg ];
          postBuild = ''
            rm -f $out/bin/cargo-hax
            install -m555 ${haxVersionScript} $out/bin/cargo-hax
          '';
        };

        aeneasPkg = aeneas.packages.${system}.default;
        aeneasRev = aeneas.rev;
        aeneasVersionScript = pkgs.writeShellScript "aeneas" ''
          case " $* " in
            *" -version "*)
              echo "aeneas ${aeneasRev}"
              exit 0
              ;;
          esac
          exec ${aeneasPkg}/bin/aeneas "$@"
        '';
        aeneasWrapped = pkgs.symlinkJoin {
          name = "aeneas-version-wrapped";
          paths = [ aeneasPkg ];
          postBuild = ''
            rm -f $out/bin/aeneas
            install -m555 ${aeneasVersionScript} $out/bin/aeneas
          '';
        };
      in
      {
        devShells.default = pkgs.mkShell (tools-environment // {
          packages = [
            pkgs.clang_18
            pkgs.llvmPackages_18.clang-tools
            (pkgs.writeShellScriptBin "clang-format-18" ''exec ${pkgs.llvmPackages_18.clang-tools}/bin/clang-format "$@"'')
            pkgs.cmake
            pkgs.ninja
            pkgs.openssl
            pkgs.pkg-config
            pkgs.jq
            pkgs.valgrind
            pkgs.libclang
            pkgs.python3
            pkgs.cargo-bloat
            pkgs.cargo-binutils
            # `qemu-system-arm` for emulating the nucleo-l4r5zi binaries
            # (libcrux-nucleo-l4r5zi/run-qemu.sh). Pulls in all qemu system
            # emulators; if size matters this can be narrowed in the future.
            pkgs.qemu
            pkgs.flip-link
            defmt-print
            rustToolchain
            fstar.packages.${system}.default
            hax.packages.${system}.default
          ];
          RUST_SRC_PATH = "${rustToolchain.outPath}/lib/rustlib/src/rust/library";
          LIBCLANG_PATH = "${pkgs.llvmPackages_18.libclang.lib}/lib";
        });

        # Toolchain for the SHA-3 Aeneas/Lean proof. Reproduces the
        # "Reproduction" section of
        # libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/README.md.
        #
        #   nix develop .#aeneas-lean
        #
        # Extraction (Rust -> Lean):
        #   cd libcrux-iot/sha3 && ./hax_aeneas.py
        # Proving:
        #   cd libcrux-iot/sha3/proofs/aeneas-lean
        #   lake exe cache get && lake build
        devShells.aeneas-lean = pkgs.mkShell {
          packages = [
            # Extraction: `cargo hax into aeneas-lean` + Aeneas.
            # Both are version-wrapped (see the `let` block) so the version
            # checks in hax_aeneas.py pass against the flake-locked revs.
            haxEvit # cargo-hax (+ bundled charon-driver)
            aeneasWrapped # aeneas (+ bundled charon)
            rustToolchain
            pkgs.python3 # runs hax_aeneas.py

            # Proving: elan provisions the pinned Lean toolchain (from the
            # lean-toolchain file) and provides `lake`.
            pkgs.elan

            # Common build deps for lake / native crates.
            pkgs.git
            pkgs.curl
            pkgs.cmake
            pkgs.gmp
            pkgs.pkg-config
          ];
          RUST_SRC_PATH = "${rustToolchain.outPath}/lib/rustlib/src/rust/library";
        };
      }
    );
}
