## Formal Verification of Computational Origami

A Lean formalization plus a small web UI to inspect and edit FOLD crease patterns.

### Structure
- Origami/     : Lean formalization
- data/        : FOLD files
- origami-sim/ : Web UI + Rust/WASM core

### How to run and use
You need a Rust toolchain installed (cargo + rustc).
First run can take a while because it downloads Mathlib and compiles Rust/WASM.

Clone with submodules, then run the helper script from the repo root:

```bash
git clone --recurse-submodules git@github.com:celioboulay/origami-formalization.git
cd origami-formalization
chmod +x run-origami.sh
./run-origami.sh
```

Open `http://localhost:8000/`, then:
1) Click `Edit Pattern` to enter edit mode.
2) Choose a crease type, then click-drag on the canvas to draw creases.
3) (Optional) Use `Add point` to place a standalone vertex.
4) Click `Export to Fold` to save the pattern to `./data`.
5) Click `Run Lean Check` to export, convert to Lean, and compile.
