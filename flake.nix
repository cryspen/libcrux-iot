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
    eurydice.url = "github:aeneasverif/eurydice/b227478b67c6a6e2ff611f978f10d6b7f26472ac";
    hax.url = "github:hacspec/hax";
  };

  outputs =
    { self, nixpkgs, flake-utils, rust-overlay, eurydice, hax, ... } @ inputs:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; overlays = [ rust-overlay.overlays.default ]; };
        charon = eurydice.inputs.charon;
        karamel = eurydice.packages.${system}.karamel;
        fstar = eurydice.inputs.karamel.inputs.fstar;

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
          extensions = [ "rust-src" "rust-analyzer" ];
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
