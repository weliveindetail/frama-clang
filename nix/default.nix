# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { } }:

let
     unstablePckgs = import (pkgs.fetchFromGitHub {
         # Descriptive name to make the store path easier to identify
         owner = "nixos";
         repo = "nixpkgs";
         rev = "0f0b14258be090303c5013c2e29234040fa9766c";
         sha256 = "0srpsnr5fhn2zp36jx3inj6vrs5n302hh3vv0c7rsc90aq5i27cr";
     }) {};
in
plugins.helpers.simple_plugin
   { inherit pkgs stdenv src opam2nix ocaml_version plugins;
     name = "frama-clang";
     deps = [ unstablePckgs.llvmPackages_9.clang-unwrapped unstablePckgs.llvm_9 pkgs.gnused pkgs.alt-ergo ];
     opamPackages = [ "camlp5" ];
     configure_options = "-with-clang-includedir=${unstablePckgs.llvmPackages_9.clang-unwrapped}";
     preFramaCTests = ''
       echo Configuring Why3 for frama-clang.
       export HOME=$(mktemp -d)
       why3 config --full-config
     '';
   }
