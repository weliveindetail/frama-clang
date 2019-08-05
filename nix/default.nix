# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { } }:

plugins.helpers.simple_plugin
   { inherit pkgs stdenv src opam2nix ocaml_version plugins;
     name = "frama-clang";
     deps = [ pkgs.llvmPackages_4.clang-unwrapped pkgs.llvm_4 pkgs.gnused ];
     opamPackages = [ "camlp4" ];
     postPatch = ''
     sed -i Makefile.config.in -e "s&@CLANG_INCDIR@&${pkgs.llvmPackages_4.clang-unwrapped}/include&"
     '';
   }
