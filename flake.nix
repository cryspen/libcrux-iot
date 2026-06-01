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
      }
    );
}
