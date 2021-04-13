# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml_version ? "ocamlPackages_latest.ocaml", plugins ? { },
   plugin_extend ? self: super: { }
 }:

let old_pkgs = pkgs; in

let frama_clang_build =
  { pkgs?old_pkgs,
    stdenv?pkgs.stdenv,
    llvm_version,
    llvm?pkgs.${"llvm_"+llvm_version},
    llvm_package?pkgs.${"llvmPackages_"+llvm_version} } :
(plugins.helpers.simple_plugin
   { inherit pkgs stdenv src opam2nix ocaml_version plugins plugin_extend;
     name = "frama-clang-on-llvm-" + llvm_version;
     deps = [ llvm_package.clang-unwrapped llvm pkgs.gnused ];
     opamPackages = [ { name = "camlp5"; constraint="=7.14";} ];
     preFramaCTests = ''
       echo CONFIGURING Why3 for Frama_Clang.
       export HOME=$(mktemp -d)
       why3 config detect
     '';
   });
in
let newer_nix =  pkgs.fetchFromGitHub {
    owner = "nixos";
    repo = "nixpkgs";
    rev = "bb46a6eb7c6a0faf08263e0564c51910bfbd83c7";
    sha256 = "15w1321wbm3vpk4qmj6d9pz3y522c0q32gkccj82c3fandb9ppj6";
    fetchSubmodules = true;
};
in
let new_pkgs = import newer_nix {};
in
(frama_clang_build { llvm_version="9"; })
  .extend(
    self: super:
    { on-llvm10 = (frama_clang_build { llvm_version="10"; });
      on-llvm11 = (frama_clang_build { pkgs = new_pkgs; llvm_version="11";});
    })
