# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { } }:

let
     unstablePckgs = import (builtins.fetchGit {
         # Descriptive name to make the store path easier to identify
         name = "With-RTTI-fix";
         url = "https://github.com/NixOS/nixpkgs/";
         ref = "master";
         rev = "0f0b14258be090303c5013c2e29234040fa9766c";
     }) {};
in
plugins.helpers.simple_plugin
   { inherit pkgs stdenv src opam2nix ocaml_version plugins;
     name = "frama-clang";
     deps = [ unstablePckgs.llvmPackages_9.clang-unwrapped unstablePckgs.llvm_9 pkgs.gnused ];
     opamPackages = [ "camlp5" ];
     configure_options = "-with-clang-includedir=${unstablePckgs.llvmPackages_9.clang-unwrapped}";
   }
