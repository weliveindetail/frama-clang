#To copy in other repository
{ pkgs ? import <nixpkgs> {}, password}:

let
    src = builtins.fetchGit {
            "url" = "https://bobot:${password}@git.frama-c.com/frama-c/Frama-CI.git";
            "name" = "Frama-CI";
            "rev" = "0bea80e8c469f9a623e7057be52c382f3967a4b8";
            "ref" = "feature/pure-local-launch";
    };
 in
 {
  src = src;
  compiled = pkgs.callPackage "${src}/compile.nix" { inherit pkgs; };
 }
