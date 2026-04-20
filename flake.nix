# =============================================================================
# agda-algebras — Nix flake
#
# File: flake.nix
#
# Goals:
#
#   1. `nix develop` from the repo root drops you in a shell with exactly the
#      Agda / stdlib versions agda-algebras 2.0 targets. No ~/.config/agda
#      configuration required (or consulted).
#   2. Reproducibility via flake.lock. The nixpkgs input pin *is* the Agda/
#      stdlib pin.
#   3. The shell writes a project-local AGDA_DIR that overrides anything in
#      the user's ~/.config/agda/ (e.g. a globally-registered stdlib 2.2).
#
# Pinning Policy:
#
#   A single nixpkgs input on nixos-unstable supplies both Agda (2.8.0) and
#   its standard library (2.3). `nix flake update` pulls in whatever
#   nixos-unstable has at update time — use deliberately.
#
#   If/when nixpkgs moves its Agda or stdlib past our target versions before
#   agda-algebras is ready to follow, the right fix is to either
#   (a) stop calling `nix flake update`, or
#   (b) add `overrideAttrs` block here pinning stdlib's `src` to a specific v2.3 tag.
#
# Library Resolution:
#
#   agda-stdlib's own standard-library.agda-lib at tag v2.3 declares
#   `name: standard-library-2.3`.  Agda resolves library dependencies as:
#     - `depend: standard-library`     — any version
#     - `depend: standard-library-2.3` — exact match required
#
#   Division of responsibilities:
#     - flake.lock               pins the stdlib source of truth.
#     - --library standard-library (wrapper) tracks whatever the lock pins.
#     - depend: standard-library-2.3 (.agda-lib) enforces the minimum.
#
#   Upgrading past 2.3 is a two-step process: bump the .agda-lib floor first,
#   then `nix flake update`. Skipping the first step produces a clear
#   dependency-resolution error at `make check` time, not a silent upgrade.
# =============================================================================
{
  description = "agda-algebras — a formalization of Universal Algebra in Agda";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      # ---- Supported systems ----------------------------------------------
      systems = [
        "x86_64-linux"     # e.g., a ThinkPad X1
        "aarch64-linux"    # e.g., a Jetson AGX Orin
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      # Per-system attrset: { system = f { pkgs }; }.
      # Matches the pattern used in the agda-native-air flake.
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system:
          f { pkgs = import nixpkgs { inherit system; }; });

      # ---- Agda + stdlib --------------------------------------------------
      # Agda and its stdlib MUST be resolved from the same package set;
      # agdaPackages.standard-library is built against pkgs.agda.
      mkAgdaEnv = pkgs: pkgs.agda.withPackages (p: [ p.standard-library ]);

      # ---- Project-local AGDA_DIR + agda() wrapper ------------------------
      # Writes $ROOT/.agda/{libraries,defaults} and defines an agda() shell
      # function that bypasses the Nix wrapper's baked-in --library-file by
      # passing --library-file again on the command line (Agda's last-flag-
      # wins rule). This also passes --no-default-libraries so the user's
      # ~/.config/agda/defaults (if any) cannot contribute.
      mkAgdaShellSetup = agdaStdlibPkg: ''
        # ---- Locate repo root (git, with $PWD fallback) ----
        ROOT="$PWD"
        if command -v git >/dev/null 2>&1 && git rev-parse --show-toplevel >/dev/null 2>&1; then
          ROOT="$(git rev-parse --show-toplevel)"
        fi

        # ---- AGDA_DIR: project-local, gitignored ----
        export AGDA_DIR="$ROOT/.agda"
        mkdir -p "$AGDA_DIR"

        # libraries file: absolute paths to .agda-lib files Agda should know
        # about in this shell. Order doesn't matter; both are resolvable.
        {
          echo "${agdaStdlibPkg}/standard-library.agda-lib"
          echo "$ROOT/agda-algebras.agda-lib"
        } > "$AGDA_DIR/libraries"

        # defaults file: libraries auto-loaded when a file has no .agda-lib
        # ancestor. We only put stdlib here; agda-algebras is picked up via
        # auto-discovery from the repo-root .agda-lib.
        echo "standard-library" > "$AGDA_DIR/defaults"

        # Capture the absolute path to the Nix-wrapped agda BEFORE we prepend
        # our own wrapper to PATH; otherwise the script would recursively call
        # itself.
        NIX_AGDA="$(command -v agda)"
        mkdir -p "$AGDA_DIR/bin"
        cat > "$AGDA_DIR/bin/agda" <<EOF
#!/usr/bin/env bash
exec "$NIX_AGDA" \\
  --no-default-libraries \\
  --library-file "$AGDA_DIR/libraries" \\
  --library standard-library \\
  --library agda-algebras \\
  "\$@"
EOF
        chmod +x "$AGDA_DIR/bin/agda"
        export PATH="$AGDA_DIR/bin:$PATH"
      '';
    in {
      # ---- Formatter -------------------------------------------------------
      formatter = forAllSystems ({ pkgs }: pkgs.nixpkgs-fmt);

      # ---- Dev shell -------------------------------------------------------
      devShells = forAllSystems ({ pkgs }:
        let
          agdaEnv = mkAgdaEnv pkgs;
          stdlibVer = pkgs.agdaPackages.standard-library.version;
          agdaVer = pkgs.agda.version;
        in {
          default = pkgs.mkShell {
            name = "agda-algebras-dev";

            packages = [
              agdaEnv
              pkgs.gnumake
              pkgs.git
            ];

            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";

            shellHook = ''
              ${mkAgdaShellSetup pkgs.agdaPackages.standard-library}

              echo ""
              echo "✅ agda-algebras dev shell"
              echo "   Agda   : ${agdaVer}    ($(agda --version 2>/dev/null | head -n1))"
              echo "   stdlib : ${stdlibVer}"
              echo "   AGDA_DIR : $AGDA_DIR"
              echo "   repo   : $ROOT"
              echo ""

              # Version-floor sanity checks. These are warnings, not errors —
              # a higher stdlib/Agda may still work, and the user has opted
              # into it via `nix flake update`.
              case "${agdaVer}" in
                2.8.*) : ;;
                *) echo "⚠  expected Agda 2.8.x, got ${agdaVer}" ;;
              esac
              case "${stdlibVer}" in
                2.3*) : ;;
                *) echo "⚠  expected standard-library 2.3, got ${stdlibVer}" ;;
              esac
            '';
          };
        });

      # ---- Packages (handy for CI and downstream flakes) -------------------
      packages = forAllSystems ({ pkgs }: {
        default = mkAgdaEnv pkgs;
      });

      # ---- Minimal overlay for downstream consumers ------------------------
      overlays.default = final: _prev: {
        agda-algebras-agda = mkAgdaEnv final;
      };
    };
}
