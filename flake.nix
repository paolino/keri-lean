{
  description = "keri-lean — Lean 4 formalization of KERI protocol invariants";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    dev-assets-mkdocs.url = "github:paolino/dev-assets?dir=mkdocs";
  };

  outputs =
    inputs@{
      self,
      flake-parts,
      nixpkgs,
      dev-assets-mkdocs,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      perSystem =
        { system, pkgs, ... }:
        let
          mkdocsEnv = dev-assets-mkdocs.devShells.${system}.default;
        in
        {
          devShells.default = pkgs.mkShell {
            inputsFrom = [ mkdocsEnv ];
            packages = [
              pkgs.just
              pkgs.elan
            ];
          };
        };
    };
}
