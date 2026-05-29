#!/usr/bin/env bash
# =============================================================================
# agda-algebras — Claude Code SessionStart hook
#
# File: .claude/hooks/session-start.sh
#
# Purpose
#   Provision the Agda toolchain inside an ephemeral "Claude Code on the web"
#   container so the agent can type-check the library exactly like CI does:
#
#       nix develop --command make check
#
#   The container is wiped between sessions, so this runs fresh each time.
#   It is deliberately idempotent: re-running it on a warm container is cheap.
#
# What it does
#   1. Installs Nix (single-user) if not already present, fetching the
#      installer + tarball from releases.nixos.org.
#   2. Writes /etc/nix/nix.conf enabling flakes and configuring single-user
#      (rootless-build) operation against the public binary cache.
#   3. Pre-warms the project dev shell so Agda 2.8.0 + standard-library 2.3
#      (pinned by flake.lock) are realised from cache.nixos.org up front.
#   4. Persists PATH / SSL env into $CLAUDE_ENV_FILE so `nix` is available to
#      every shell in the session.
#
# Toolchain pinning lives in flake.nix / flake.lock — NOT here. This script
# only needs to make `nix` work; the flake decides which Agda/stdlib you get.
#
# Network note
#   The web container uses a host allowlist. nixos.org and
#   install.determinate.systems are NOT reachable, but releases.nixos.org and
#   cache.nixos.org ARE — so we fetch the installer straight from
#   releases.nixos.org rather than the usual nixos.org/nix/install redirector.
#
# Mode: synchronous (the session waits until provisioning finishes). This
# prevents the agent from invoking `agda` before it exists. To trade that
# guarantee for faster startup, switch to async (see the skill docs).
# =============================================================================
set -euo pipefail

# ---- Web-only -------------------------------------------------------------
# Locally, developers use `nix develop` directly; this hook is just for the
# remote (Claude Code on the web) container.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  echo "session-start: not a remote session — skipping Nix provisioning."
  exit 0
fi

NIX_VERSION="2.31.2"
PROFILE_NIX="/root/.nix-profile/bin/nix"

log() { echo "session-start: $*"; }

# ---- 1. Global Nix config (written before install so the installer's own
#         profile step succeeds in a container with no 'nixbld' group) -------
write_nix_conf() {
  mkdir -p /etc/nix
  cat > /etc/nix/nix.conf <<'CONF'
# Managed by .claude/hooks/session-start.sh — single-user, rootless builds.
experimental-features = nix-command flakes
build-users-group =
sandbox = false
substituters = https://cache.nixos.org https://formalverification.cachix.org
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= formalverification.cachix.org-1:<PASTE_KEY_FROM_cachix_use>
max-jobs = auto
CONF
}

# ---- 2. Install Nix if absent --------------------------------------------
install_nix() {
  if [ -x "$PROFILE_NIX" ] && "$PROFILE_NIX" --version >/dev/null 2>&1; then
    log "Nix already installed ($("$PROFILE_NIX" --version))."
    return 0
  fi

  local arch system installer
  arch="$(uname -m)"
  case "$arch" in
    x86_64)  system="x86_64-linux"  ;;
    aarch64) system="aarch64-linux" ;;
    *) echo "session-start: unsupported arch '$arch'" >&2; exit 1 ;;
  esac

  log "Installing Nix ${NIX_VERSION} for ${system} ..."
  installer="$(mktemp -t nix-install.XXXXXX.sh)"
  # releases.nixos.org is allowlisted; the bootstrap script fetches the
  # matching tarball from the same host.
  curl -fsSL "https://releases.nixos.org/nix/nix-${NIX_VERSION}/install" -o "$installer"

  # Single-user install. Config is already in place so the internal
  # `nix-env -i` profile step succeeds without a build-users group.
  sh "$installer" --no-daemon --yes || true
  rm -f "$installer"

  # Fallback: if the profile link didn't get created, register the freshly
  # unpacked store path into root's profile by hand.
  if [ ! -x "$PROFILE_NIX" ]; then
    local store_nix
    store_nix="$(ls -d /nix/store/*-nix-${NIX_VERSION} 2>/dev/null | head -1 || true)"
    if [ -n "$store_nix" ]; then
      log "Completing profile install from ${store_nix}"
      "${store_nix}/bin/nix-env" -i "$store_nix"
    fi
  fi

  [ -x "$PROFILE_NIX" ] || { echo "session-start: Nix install failed" >&2; exit 1; }
  log "Installed $("$PROFILE_NIX" --version)."
}

# ---- 3. Session environment ----------------------------------------------
# Make `nix` available to every shell the agent spawns, and point Nix at the
# system CA bundle for HTTPS substituter access.
setup_env() {
  export PATH="/root/.nix-profile/bin:/nix/var/nix/profiles/default/bin:$PATH"

  local cert
  for cert in /etc/ssl/certs/ca-certificates.crt \
              /etc/ssl/certs/ca-bundle.crt \
              /etc/pki/tls/certs/ca-bundle.crt; do
    [ -f "$cert" ] && export NIX_SSL_CERT_FILE="$cert" && break
  done

  if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
    {
      echo "export PATH=\"/root/.nix-profile/bin:/nix/var/nix/profiles/default/bin:\$PATH\""
      [ -n "${NIX_SSL_CERT_FILE:-}" ] && echo "export NIX_SSL_CERT_FILE=\"${NIX_SSL_CERT_FILE}\""
    } >> "$CLAUDE_ENV_FILE"
  fi
}

# ---- 4. Pre-warm the dev shell -------------------------------------------
# Realise Agda 2.8.0 + standard-library 2.3 from the binary cache now, so the
# first real `nix develop --command ...` in the session is instant.
warm_flake() {
  local root="${CLAUDE_PROJECT_DIR:-$PWD}"
  log "Warming dev shell from ${root}/flake.nix ..."
  ( cd "$root" && nix develop --command bash -c 'agda --version' ) \
    && log "Toolchain ready." \
    || { echo "session-start: warning — dev shell warm-up failed" >&2; return 1; }
}

write_nix_conf
install_nix
setup_env
warm_flake || log "warm-up deferred — first 'nix develop' will realize the closure"

log "Done. Type-check with:  nix develop --command make check"
