# paramaterised derivation with dependencies injected (callPackage style)
 { pkgs, stdenv, src ? ../., opam2nix,
   ocaml ? "ocamlPackages_latest.ocaml", plugins ? { },
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
   { inherit pkgs stdenv src opam2nix ocaml plugins plugin_extend;
     name = "frama-clang-on-llvm-" + llvm_version;
     deps = [ llvm_package.clang-unwrapped llvm pkgs.gnused ];
     opamPackages = [ "camlp5=7.14" ];
     preFramaCTests = ''
       echo CONFIGURING Why3 for Frama_Clang.
       export HOME=$(mktemp -d)
       why3 config detect
     '';
   });
in
(frama_clang_build { llvm_version="9"; })
  .extend(
    self: super:
    { on-llvm10 = (frama_clang_build { llvm_version="10"; });
      on-llvm11 = (frama_clang_build { llvm_version="11"; });
    })
