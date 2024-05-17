# flake.nix
# This file defines a Nix flake for the agda-algebras project, providing a
# reproducible and versioned environment including Agda and its standard library.

# Objective: This configuration file and instructions should help any user set up and work
# with the `agda-algebras` project using Nix or NixOS.

# Flake description and inputs.
{
  description = "agda-algebras project with Agda and the Agda Standard Library";

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

      # Optional: Define a package build environment (if needed).
      packages.agda-algebras = pkgs.buildFHSUserEnv {
        name = "agda-algebras";
        targetPkgs = pkgs: [
          pkgs.agda                    # The Agda programming language.
          pkgs.agdaPackages.standard-library  # The Agda standard library.
        ];
        runScript = "agda --library-file=${./agda-algebras.agda-lib} src/Main.agda";
      };
    };
}

# Usage:
# 1. Ensure Nix is installed on your system.
# 2. Enable flakes by adding 'experimental-features = nix-command flakes' to your ~/.config/nix/nix.conf.
# 3. Navigate to the project directory.
# 4. Run `nix develop` to enter the development environment with Agda and its standard library configured.

# More details:
# +  Using `default.nix`
#    + This is the traditional method for setting up the environment.
#    + In the project directory, run `nix-shell`.
#    + This command will drop you into a shell where Agda and the standard library are available and configured.
# + Using `flake.nix`:
#   + This method is for those who want the benefits of flakes, including better reproducibility and versioning.
#   + Enable flakes by adding `experimental-features = nix-command flakes` to your `~/.config/nix/nix.conf`.
#   + In the project directory, run `nix develop`.
#   + This command will drop you into a development environment with Agda and the standard library configured.

# + Important parts of this file
#   +  `pkgs.mkShell` is used to define a development shell with specific build inputs (dependencies).
#      It's essential for setting up the environment with the necessary tools.
#   +  `buildInputs` is a list of packages to include in the environment. Here, it includes Agda and the
#      Agda standard library.
#   +  `AGDA_LIBS` is an environment variable that Agda uses to locate the library file.
#      This is crucial for Agda to find the necessary library paths.
#   +  `inputs.nixpkgs.url` in `flake.nix` specifies the source of the Nix packages, typically from the
#      official Nixpkgs repository.
#   +  `outputs` defines what the flake will produce, such as development environments or packages.
