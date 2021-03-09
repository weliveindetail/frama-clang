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
