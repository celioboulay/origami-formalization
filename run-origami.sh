#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SIM_DIR="$ROOT_DIR/origami-sim"
WEB_DIR="$SIM_DIR/web"
PORT="${PORT:-8000}"

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

echo "==> Building wasm (origami-sim)"
(
  cd "$SIM_DIR"
  wasm-pack build --target web --out-dir web/pkg --release
)

echo "==> Starting web server at http://localhost:$PORT"
if command -v python3 >/dev/null 2>&1; then
  (cd "$WEB_DIR" && python3 -m http.server "$PORT")
elif command -v python >/dev/null 2>&1; then
  (cd "$WEB_DIR" && python -m http.server "$PORT")
else
  echo "Python is required to serve the web folder. Install Python 3." >&2
  exit 1
fi
