# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { } }:

let frama_clang_build =
  { llvm_version,
    llvm?pkgs.${"llvm_"+llvm_version},
    llvm_package?pkgs.${"llvmPackages_"+llvm_version} } :

(plugins.helpers.simple_plugin
   { inherit pkgs stdenv src opam2nix ocaml_version plugins;
     name = "frama-clang-on-llvm-" + llvm_version;
     deps = [ llvm_package.clang-unwrapped llvm pkgs.gnused ];
     opamPackages = [ { name = "camlp5"; constraint="=7.14";} ];
     preFramaCTests = ''
       echo CONFIGURING Why3 for Frama_Clang.
       export HOME=$(mktemp -d)
       why3 config --detect
     '';
   });
in
(frama_clang_build { llvm_version="9"; })
// { on-llvm10 = (frama_clang_build { llvm_version="10"; });}
// { on-llvm11 = (frama_clang_build { llvm_version="11"; });}
