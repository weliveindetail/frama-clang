# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { } }:

plugins.helpers.simple_plugin
   { inherit pkgs stdenv src opam2nix ocaml_version plugins;
     name = "frama-clang";
     deps = [ pkgs.llvmPackages_9.clang-unwrapped pkgs.llvm_9 pkgs.gnused ];
     opamPackages = [ "camlp5" ];
     configure_options = "-with-clang-includedir=${pkgs.llvmPackages_9.clang-unwrapped}";
   }
