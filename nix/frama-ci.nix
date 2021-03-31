#To copy in other repository
{ pkgs ? import <nixpkgs> {}, password}:

let
    src = builtins.fetchGit {
            "url" = "https://bobot:${password}@git.frama-c.com/frama-c/Frama-CI.git";
            "name" = "Frama-CI";
            "rev" = "f9e0cd6c067f424cfe13abc7a8de49a8da43160f";
            "ref" = "feature/pure-local-launch";
    };
 in
 {
  src = src;
  compiled = pkgs.callPackage "${src}/compile.nix" { inherit pkgs; };
 }
