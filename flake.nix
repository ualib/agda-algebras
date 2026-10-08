# =============================================================================
# agda-algebras — Nix flake
#
# File: flake.nix
#
# Goals:
#
#   1. `nix develop` from the repo root drops you in a shell with exactly the
#      Agda / stdlib versions agda-algebras 3.0 targets. No ~/.config/agda
#      configuration required (or consulted).
#   2. Reproducibility: flake.lock pins nixpkgs and Agda's own flake, and the
#      standard library is pinned below by commit and hash.
#   3. The shell writes a project-local AGDA_DIR that overrides anything in
#      the user's ~/.config/agda/ (e.g. a globally-registered stdlib 2.2).
#
# Pinning Policy:
#
#   Agda 2.9.0 is not released yet, and no released standard library
#   type-checks under it, so until both are released the flake pins them
#   itself, as follows:
#
#     +  Agda comes from the `agda` input: agda/agda at a fixed commit, the
#        `nightly` of 2026-10-05, built from source by Agda's own flake (its
#        `base` package, without the `debug` flag of its default build).
#        nixpkgs' Agda package set is rebuilt around it (mkAgdaPackages).
#        The input's URL names the commit, so `nix flake update` cannot
#        move it; to move it, edit the URL and the standard library together.
#     +  The standard library is nixpkgs' derivation with its `src` moved to
#        formalverification/agda-stdlib's tag v2.3-agda-2.9.0: v2.3 with the
#        five changes it needs to type-check under Agda 2.9.0, which that
#        tag's release notes list (stdlibRev and stdlibHash, below).
#
#   The nixpkgs input still supplies the package-set machinery and the rest
#   of the shell.  Once Agda 2.9.0 and a standard library for it are
#   released and nixpkgs packages them, drop the `agda` input and the
#   standard library's override, and return to one nixpkgs input on
#   nixos-unstable supplying both.
#
# Library Resolution:
#
#   agda-stdlib's own standard-library.agda-lib at tag v2.3 declares
#   `name: standard-library-2.3`, and so does the patched v2.3 the flake
#   pins.  Agda resolves library dependencies as:
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
    # Agda 2.9.0, unreleased: agda/agda at the commit of the `nightly` of
    # 2026-10-05.  Agda's flake builds it with its own nixpkgs; do not make
    # it follow ours.  Its tree holds six empty directories (the paths of
    # its submodules), which Nix 2.26.3 drops when it unpacks the tree, so
    # that it computes another hash than the one flake.lock records: this
    # flake needs Nix 2.28 or later (2.28.6 and 2.35.2 agree on the hash).
    agda.url = "github:agda/agda/da66a8c75f11d10699a6b38b261efdf244b66f2a";
  };

  outputs = { self, nixpkgs, agda }:
    let
      # ---- Supported systems ----------------------------------------------
      systems = [
        "x86_64-linux"     # e.g., a ThinkPad X1
        "aarch64-linux"    # e.g., a Jetson AGX Orin
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      # Per-system attrset: { system = f { system, pkgs }; }.
      # Matches the pattern used in the agda-native-air flake.
      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system:
          f { inherit system; pkgs = import nixpkgs { inherit system; }; });

      # ---- Agda + stdlib --------------------------------------------------
      # Agda and its stdlib MUST be resolved from the same package set:
      # nixpkgs' Agda package set, rebuilt around the `agda` input's Agda,
      # with the standard library's source moved to the patched v2.3 (see
      # the header).
      #
      # To move the standard library, set stdlibRev, put nixpkgs.lib.fakeHash
      # in stdlibHash's place, run `nix build`, and copy the hash the error
      # prints after `got:`; or ask Nix for it directly:
      #   nix flake prefetch --json github:formalverification/agda-stdlib/<rev> | jq -r .hash
      stdlibRev  = "fb5d1840d26909038b5ae1459733b0db425a7488";
      stdlibHash = "sha256-ZF+/2bUhKggpGY0WtHqKkOstRTGe8LOhK4lD+4T3xSc=";

      mkAgdaPackages = system: pkgs:
        let
          agdaPackages = pkgs.agdaPackages.override {
            Agda = agda.packages.${system}.base;
          };
        in {
          inherit (agdaPackages) agda;
          standard-library = agdaPackages.standard-library.overrideAttrs (_: {
            version = "2.3-agda-2.9.0";
            src = pkgs.fetchFromGitHub {
              owner = "formalverification";
              repo = "agda-stdlib";
              rev = stdlibRev;
              hash = stdlibHash;
            };
          });
        };

      mkAgdaEnv = ap: ap.agda.withPackages [ ap.standard-library ];

      # ---- Python environment (docs pipeline + script tooling) ------------
      # ONE python3.withPackages environment serves the whole repo, and it
      # must stay one: two withPackages interpreters on the same PATH shadow
      # each other rather than merge, so every Python dependency of the repo
      # belongs in this list.
      #
      # The list is the MkDocs rendering pipeline (ADR-007).  `make site` and
      # `make serve` build the documentation site directly from the
      # `.lagda.md` sources, with no `agda --html` step, relying on kramdown
      # attribute spans and custom CSS for inline Agda highlighting.  Pinning
      # the whole stack here makes `nix develop --command make site`
      # reproduce CI's site build exactly, the same way the Agda env
      # reproduces `make check`.  mkdocs-material transitively supplies
      # pymdown-extensions (attr_list / snippets), but we list it explicitly
      # to document intent.  The rest of the script tooling under
      # scripts/python/ is stdlib-only by design, so it adds nothing here.
      mkPythonEnv = pkgs: pkgs.python3.withPackages (p: [
        # -- documentation site (ADR-007) --
        p.mkdocs                  # static-site generator
        p.mkdocs-material         # Material theme
        p.mkdocs-macros           # {{ vars }} / Jinja2 site variables
        p.mkdocs-redirects        # legacy Module.Submodule.html → new URLs
        p.mkdocs-gen-files        # mount src/**/*.lagda.md as site pages
        p.mkdocs-literate-nav     # library nav from a generated SUMMARY.md
        p.mkdocs-section-index    # clickable section-landing pages
        p.pymdown-extensions      # attr_list companions + snippets auto_append
      ]);

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
      formatter = forAllSystems ({ pkgs, ... }: pkgs.nixpkgs-fmt);

      # ---- Dev shell -------------------------------------------------------
      devShells = forAllSystems ({ system, pkgs }:
        let
          agdaPkgs = mkAgdaPackages system pkgs;
          agdaEnv = mkAgdaEnv agdaPkgs;
          pythonEnv = mkPythonEnv pkgs;
          stdlibVer = agdaPkgs.standard-library.version;
          agdaVer = agdaPkgs.agda.version;
          mkdocsVer = pkgs.python3Packages.mkdocs.version;
          materialVer = pkgs.python3Packages.mkdocs-material.version;
        in {
          default = pkgs.mkShell {
            name = "agda-algebras-dev";

            packages = [
              agdaEnv
              pythonEnv
              pkgs.gnumake
              pkgs.git
            ];

            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";

            shellHook = ''
              ${mkAgdaShellSetup agdaPkgs.standard-library}

              echo ""
              echo "✅ agda-algebras dev shell"
              echo "   Agda     : ${agdaVer}    ($(agda --version 2>/dev/null | head -n1))"
              echo "   stdlib   : ${stdlibVer}"
              echo "   MkDocs   : ${mkdocsVer} + Material ${materialVer}  (make site / make serve)"
              echo "   AGDA_DIR : $AGDA_DIR"
              echo "   repo     : $ROOT"
              echo ""

              # Version-floor sanity checks. These are warnings, not errors —
              # a higher stdlib/Agda may still work, and the user has opted
              # into it via `nix flake update`.
              case "${agdaVer}" in
                2.9.*) : ;;
                *) echo "⚠  expected Agda 2.9.x, got ${agdaVer}" ;;
              esac
              case "${stdlibVer}" in
                2.3*) : ;;
                *) echo "⚠  expected standard-library 2.3, got ${stdlibVer}" ;;
              esac
            '';
          };
        });

      # ---- Packages (handy for CI and downstream flakes) -------------------
      packages = forAllSystems ({ system, pkgs }: {
        default = mkAgdaEnv (mkAgdaPackages system pkgs);
      });

      # ---- Minimal overlay for downstream consumers ------------------------
      overlays.default = final: _prev: {
        agda-algebras-agda =
          mkAgdaEnv (mkAgdaPackages final.stdenv.hostPlatform.system final);
      };
    };
}
