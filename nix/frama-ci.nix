#To copy in other repository
{ pkgs, password}:

let
    src = builtins.fetchGit {
            "url" = "https://bobot:${password}@git.frama-c.com/frama-c/Frama-CI.git";
            "name" = "Frama-CI";
            "rev" = "f86e807d6f440ac4479b78f8419dfd817803419d";
            "ref" = "feature/wp/versions-bump";
    };
 in
 {
  src = src;
  compiled = pkgs.callPackage "${src}/compile.nix" { inherit pkgs; };
 }
