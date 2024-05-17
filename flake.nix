{
  description = "agda-algebras library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
  };

  outputs = { self, nixpkgs }: {
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
          homepage = "https://github.com/ualib/agda-algebras";  # Replace with your actual GitHub username and repository name
        };
      };
    };

    # Define devShells for each system.
    devShells = {
      x86_64-linux = import nixpkgs {
        overlays = [ self.overlay ];
      }.mkShell {
        buildInputs = [
          import nixpkgs {
            overlays = [ self.overlay ];
          }.haskellPackages.agda-algebras
        ];

        # Set the AGDA_LIBS environment variable to point to the .agda-lib file.
        AGDA_LIBS = "${self}/agda-algebras.agda-lib";
      };

      aarch64-linux = import nixpkgs {
        overlays = [ self.overlay ];
      }.mkShell {
        buildInputs = [
          import nixpkgs {
            overlays = [ self.overlay ];
          }.haskellPackages.agda-algebras
        ];

        # Set the AGDA_LIBS environment variable to point to the .agda-lib file.
        AGDA_LIBS = "${self}/agda-algebras.agda-lib";
      };
    };

    # Optionally, define packages if needed.
    packages = {
      x86_64-linux = import nixpkgs {
        overlays = [ self.overlay ];
      }.stdenv.mkDerivation {
        name = "agda-algebras";
        src = self;
        buildInputs = [
          import nixpkgs {
            overlays = [ self.overlay ];
          }.haskellPackages.agda-algebras
        ];
      };

      aarch64-linux = import nixpkgs {
        overlays = [ self.overlay ];
      }.stdenv.mkDerivation {
        name = "agda-algebras";
        src = self;
        buildInputs = [
          import nixpkgs {
            overlays = [ self.overlay ];
          }.haskellPackages.agda-algebras
        ];
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
