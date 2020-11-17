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
     mk_framac_clang = { name, llvmPackages, llvm } :
       plugins.helpers.simple_plugin
         { inherit pkgs stdenv src opam2nix ocaml_version plugins name;
           deps = [ llvmPackages.clang-unwrapped llvm pkgs.gnused ];
           opamPackages = [ "camlp5" ];
           preFramaCTests = ''
             echo CONFIGURING Why3 for Frama_Clang.
             export HOME=$(mktemp -d)
             why3 config --detect
           '';
         }    
     ;
in
(mk_framac_clang { name = "frama-clang-on-llvm-9";
                   llvmPackages = unstablePckgs.llvmPackages_9;
                   llvm = unstablePckgs.llvm_9; }) //
    { on-llvm10 = (mk_framac_clang { name = "frama-clang-on-llvm-10";
                                     llvmPackages = unstablePckgs.llvmPackages_10;
                                     llvm = unstablePckgs.llvm_10; }); }
