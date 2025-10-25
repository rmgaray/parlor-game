{
  description = "devShell for parlor-game";

  inputs = {
    # We temporarily use the "haskell-updates" branch of Nixpkgs to get
    # HLS 2.11, which supports code actions for the eval plugin.
    nixpkgs-hs-updates.url = "github:NixOS/nixpkgs/9bd652c4305d1f6b6b59451036fd0a44a13f78d5";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs-hs-updates,
    nixpkgs,
    pre-commit-hooks,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      ### Compiler
      ghcVersion = "ghc967";
      compiler = pkgs.haskell.compiler.${ghcVersion};
      ### Overlays
      pkgs = nixpkgs.legacyPackages.${system}.pkgs;
      # TODO: Drop haskell-updates input when HLS 2.11 lands in staging
      haskell-lsp = nixpkgs-hs-updates.legacyPackages.${system}.pkgs.haskell.packages.${ghcVersion}.haskell-language-server;
    in {
      checks = {
        pre-commit-check = pre-commit-hooks.lib.${system}.run {
          src = ./.;
          hooks = {
            ormolu.enable = true;
            cabal2nix.enable = true;
            alejandra.enable = true;
          };
        };
      };

      devShell = nixpkgs.legacyPackages.${system}.mkShell {
        inherit (self.checks.${system}.pre-commit-check) shellHook;
        nativeBuildInputs = with pkgs; [
          haskell-lsp
          cabal-install
          cabal2nix
          happy
          compiler
        ];
      };
    });
}
