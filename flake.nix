# flake.nix
# This file defines a Nix flake for the agda-algebras project, providing
# a reproducible and versioned environment with Agda and its standard library,
# and also defining an overlay for nixpkgs.

# Objective: help any Nix/NixOS user set up and work with the `agda-algebras` project.

# Flake description and inputs.
{
  description = "the agda-algebras library";

  # Define the inputs (dependencies) for the flake.
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
  };

  # Define the outputs of the flake.
  outputs = { self, nixpkgs }:
    let
      # Import Nix packages with the overlay applied.
      pkgs = import nixpkgs {
        overlays = [ self.overlay ];
      };
    in
    {
      # Define the overlay that adds the agda-algebras library to haskellPackages.
      overlay = final: prev: {
        haskellPackages = prev.haskellPackages // {
          agda-algebras = final.haskell.lib.makeHaskellPackage {
            pname = "agda-algebras";
            version = "0.1.0";
            src = self;
            libraryHaskellDepends = [ prev.agda prev.agdaPackages.standard-library ];
            license = final.lib.licenses.mit;
            description = "Agda project with standard library and agda-algebras library";
            homepage = "https://github.com/ualib/agda-algebras"; 
          };
        };
      };

      # Define the development shell environment.
      devShells.default = pkgs.mkShell {
        buildInputs = [
          pkgs.haskellPackages.agda-algebras
        ];

        # Set the AGDA_LIBS environment variable to point to the .agda-lib file.
        AGDA_LIBS = "${self}/agda-algebras.agda-lib";
      };
    };
}

# Usage:
# 1. Ensure Nix is installed on your system.
# 2. Enable flakes by adding 'experimental-features = nix-command flakes' to your ~/.config/nix/nix.conf.
# 3. Navigate to the project directory.
# 4. Run `nix develop` to enter the development environment with Agda and its standard library configured.

# To use the agda-algebras library as a Nixpkgs overlay:
# 1. Add the flake URL to your inputs in your flake.nix.
# 2. Use the overlay in your nixpkgs configuration.
# 3. Install the library via `haskellPackages.agda-algebras`.
