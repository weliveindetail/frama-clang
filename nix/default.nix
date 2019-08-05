# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { } }:

plugins.helpers.simple_plugin
   { inherit pkgs stdenv src opam2nix ocaml_version plugins;
     name = "frama-clang";
     deps = [ pkgs.clang_4 pkgs.llvm_4 ];
     opamPackages = [ "camlp4" ];
   }
