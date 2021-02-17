#To copy in other repository
{ pkgs ? import <nixpkgs> {}, password}:

let
    src = builtins.fetchGit {
            "url" = "https://bobot:${password}@git.frama-c.com/frama-c/Frama-CI.git";
            "name" = "Frama-CI";
            "rev" = "285cc9569c1ae0bfadb51320ba7d1d4c73b6bba0";
            "ref" = "master";
    };
 in
 {
  src = src;
  compiled = pkgs.callPackage "${src}/compile.nix" { inherit pkgs; };
 }
