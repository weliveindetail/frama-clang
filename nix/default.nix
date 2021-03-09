# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { } }:

let
     unstablePckgs = import (pkgs.fetchFromGitHub {
         # Descriptive name to make the store path easier to identify
         owner = "nixos";
         repo = "nixpkgs";
         rev = "8d327040c03fe8afbc2a2a9973af17b0d1a77bf4";
         sha256 = "0nqlyqwhb8lr1g9mwia0k2f9h91zj0vfjmaijk6z8daspsci854c";
     }) {};
in
let frama_clang_build =
  { llvm_version,
    llvm?unstablePckgs.${"llvm_"+llvm_version},
    llvm_package?unstablePckgs.${"llvmPackages_"+llvm_version} } :

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
