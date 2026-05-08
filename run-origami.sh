#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SIM_DIR="$ROOT_DIR/origami-sim"
WEB_DIR="$SIM_DIR/web"
PORT="${PORT:-8000}"
SERVER_SCRIPT="$ROOT_DIR/origami_server.py"

if [[ ! -d "$SIM_DIR" ]]; then
  echo "origami-sim not found. Make sure you cloned with --recurse-submodules." >&2
  exit 1
fi

if ! command -v wasm-pack >/dev/null 2>&1; then
  echo "wasm-pack is required. Install it: https://rustwasm.github.io/wasm-pack/installer/" >&2
  exit 1
fi

if ! command -v cargo >/dev/null 2>&1; then
  echo "Rust (cargo) is required. Install it: https://www.rust-lang.org/tools/install" >&2
  exit 1
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "Lake is required. Install it with elan: https://leanprover-community.github.io/get_started.html" >&2
  exit 1
fi

echo "==> Fetching Lean caches (lake exe cache get)"
(
  cd "$ROOT_DIR"
  lake exe cache get
)

echo "==> Building wasm (origami-sim)"
(
  cd "$SIM_DIR"
  wasm-pack build --target web --out-dir web/pkg --release
)

if [[ ! -f "$SERVER_SCRIPT" ]]; then
  echo "origami_server.py not found. Make sure you're running from the repo root." >&2
  exit 1
fi

echo "==> Starting web server at http://localhost:$PORT"
if command -v python3 >/dev/null 2>&1; then
  (cd "$ROOT_DIR" && python3 "$SERVER_SCRIPT" --port "$PORT")
elif command -v python >/dev/null 2>&1; then
  (cd "$ROOT_DIR" && python "$SERVER_SCRIPT" --port "$PORT")
else
  echo "Python is required to serve the web folder. Install Python 3." >&2
  exit 1
fi
