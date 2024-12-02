# default.nix
# This file sets up a Nix shell for the agda-algebras project, providing
# all the necessary dependencies, such as Agda and the Agda standard library.
# Users can enter this environment by running `nix-shell` in the agda-algebras
# project directory.

# Import the Nix package set.
{ pkgs ? import <nixpkgs> {} }:

# Define a shell environment using pkgs.mkShell.
pkgs.mkShell {
  # List of dependencies to include in the shell environment.
  buildInputs = [
    pkgs.agda                    # The Agda programming language.
    pkgs.agdaPackages.standard-library  # The Agda standard library.
  ];

  # The AGDA_LIBS environment variable tells Agda where to find the project-specific library.
  AGDA_LIBS = "${./agda-algebras.agda-lib}";
}

# Usage:
# 1. Ensure you have Nix installed: https://nixos.org/download.html
# 2. Clone the project: git clone <project_url>
# 3. Navigate to the project directory: cd agda-algebras
# 4. Enter the Nix shell environment: nix-shell
# This will drop you into a shell with Agda, its standard library, and agda-algebras configured.

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
