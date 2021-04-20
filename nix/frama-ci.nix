#To copy in other repository
{ pkgs ? import <nixpkgs> {}, password}:

let
    src = builtins.fetchGit {
            "url" = "https://bobot:${password}@git.frama-c.com/frama-c/Frama-CI.git";
            "name" = "Frama-CI";
            "rev" = "42a28dd4a3d4355ad4ae822d08c09f56b7984ae5";
            "ref" = "feature/upgrade-opam2nix";
    };
 in
 {
  src = src;
  compiled = pkgs.callPackage "${src}/compile.nix" { inherit pkgs; };
 }
