#To copy in other repository
{ pkgs ? import <nixpkgs> {}, password}:

let
    src = builtins.fetchGit {
            "url" = "https://bobot:${password}@git.frama-c.com/frama-c/Frama-CI.git";
            "name" = "Frama-CI";
            "rev" = "e7625c0709dafafae64fc33319ba7fccae3f7070";
            "ref" = "feature/pure-local-launch";
    };
 in
 {
  src = src;
  compiled = pkgs.callPackage "${src}/compile.nix" { inherit pkgs; };
 }
