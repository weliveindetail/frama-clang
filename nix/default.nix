# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { } }:

plugins.helpers.simple_plugin
   { inherit pkgs stdenv src opam2nix ocaml_version plugins;
     name = "frama-clang";
     deps = [ pkgs.llvmPackages_7.clang-unwrapped pkgs.llvm_7 pkgs.gnused ];
     opamPackages = [ "camlp4" ];
     configure_options = "-with-clang-includedir=${pkgs.llvmPackages_7.clang-unwrapped}";
   }
