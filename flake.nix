# flake.nix
# This file defines a Nix flake for the agda-algebras project, providing
# a reproducible and versioned environment with Agda and its standard library,
# and also defining an overlay for nixpkgs.

# Objective: help any Nix/NixOS user set up and work with the `agda-algebras` project.

# Flake description and inputs.
{
  description = "the agda-algebras library";

  # Define the inputs (dependencies) for the flake.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";

  # Define the outputs of the flake.
  outputs = { self, nixpkgs }:
    let
      # Import the Nix packages.
      pkgs = import nixpkgs { };
    in
    {
      # Define the development shell environment.
      devShells.default = pkgs.mkShell {
        # List of dependencies to include in the environment.
        buildInputs = [
          pkgs.agda                    # The Agda programming language.
          pkgs.agdaPackages.standard-library  # The Agda standard library.
        ];

        # Set the AGDA_LIBS environment variable to point to the .agda-lib file.
        AGDA_LIBS = "${./agda-algebras.agda-lib}";
      };

      # Optional: Define a package build environment.
      # This section creates a custom environment for building and running
      # the agda-algebras project as a package. It's useful for packaging
      # the project or running specific build scripts.
      packages.agda-algebras = pkgs.buildFHSUserEnv {
        name = "agda-algebras";
        targetPkgs = pkgs: [
          pkgs.agda                    # The Agda programming language.
          pkgs.agdaPackages.standard-library  # The Agda standard library.
        ];
        runScript = "agda --library-file=${./agda-algebras.agda-lib} src/Main.agda";
      };

      # Define an overlay that adds the agda-algebras library to haskellPackages.
      overlays.default = final: prev: {
        haskellPackages = prev.haskellPackages // {
          agda-algebras = final.haskell.lib.makeHaskellPackage {
            pname = "agda-algebras";
            version = "0.1.0";
            src = ./.;
            libraryHaskellDepends = [ prev.agda prev.agdaPackages.standard-library ];
            license = final.lib.licenses.mit;
            description = "the agda-algebras library";
            homepage = "https://github.com/ualib/agda-algebras";
          };
        };
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
