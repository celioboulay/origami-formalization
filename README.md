## Formal Verification of Computational Origami

This repo combines a Lean formalization with a small web UI to inspect and edit FOLD crease patterns.

### Structure
- Origami/     : Lean formalization
- data/        : FOLD files
- origami-sim/ : Web UI + Rust/WASM core

### How to use
1) Start the web UI with `./run-origami.sh` and open `http://localhost:8000/`.
2) Click `Edit Pattern` to enter edit mode.
3) Choose a crease type, then click-drag on the canvas to draw creases.
4) (Optional) Use `Add point` to place a standalone vertex.
5) Click `Export to Fold` to save the pattern to `./data`.
6) Click `Run Lean Check` to export, convert to Lean, and compile.

### Run (web UI)
Clone with submodules, then run the helper script from the repo root:

```bash
git clone --recurse-submodules git@github.com:celioboulay/origami-formalization.git
cd origami-formalization
chmod +x run-origami.sh
./run-origami.sh
```

Open `http://localhost:8000/`.
