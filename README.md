## Formal Verification of Computational Origami

We aim to bridge computational folding and formal verification by encoding origami constructions as machine-checked proofs in Lean. We will formalize the FOLD specification and the Huzita–Hatori axioms, allowing fold sequences to be represented as constructive, verifiable objects. A visual editor will generate FOLD models that are automatically translated into Lean definitions.

### Our work so far

Early commit, nothing really put together yet, but you can find some Lean definitions and structures in Oriami/FOLD, and a FOLD -> Lean parser in scripts. We will update regularly.

### Quick pipeline

Run parser and compile the generated Lean module in one command:

```powershell
python scripts/parse_and_build.py --input data/simple.json --output Origami/FOLD/parsed.lean --target Origami.FOLD.parsed
```

### Architecture
- Origami/     : Lean formalization
- data/        : FOLD files
- scripts/     : conversion (FOLD → Lean)
- graphics/    : Anthony is cooking

### TODO:
- fold paper
