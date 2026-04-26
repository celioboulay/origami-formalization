import argparse
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "data" / "simple.json"
DEFAULT_OUTPUT = ROOT / "Origami" / "FOLD" / "parsed.lean"
DEFAULT_TARGET = "Origami.FOLD.parsed"


def parse_args():
    parser = argparse.ArgumentParser(description="Run parser then compile generated Lean module")
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT, help="Input FOLD JSON path")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Generated Lean path")
    parser.add_argument("--target", default=DEFAULT_TARGET, help="Lake target/module to build")
    return parser.parse_args()


def run(cmd):
    subprocess.run(cmd, cwd=ROOT, check=True)


def main():
    args = parse_args()

    parser_cmd = [
        "python",
        str(ROOT / "scripts" / "parser.py"),
        "--input",
        str(args.input),
        "--output",
        str(args.output),
    ]
    run(parser_cmd)

    build_cmd = ["lake", "build", args.target]
    run(build_cmd)

    print(f"OK: parsed '{args.input}' and built '{args.target}'")


if __name__ == "__main__":
    main()

