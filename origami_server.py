#!/usr/bin/env python3
import argparse
import json
import re
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent
WEB_DIR = ROOT_DIR / "origami-sim" / "web"
DATA_DIR = ROOT_DIR / "data"


def _safe_stem(value: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9._-]+", "_", value).strip("._")
    return cleaned or "pattern"


class OrigamiHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(WEB_DIR), **kwargs)

    def do_POST(self):
        if self.path != "/export-fold":
            self.send_error(404, "Not Found")
            return

        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length) if length > 0 else b""
        try:
            payload = json.loads(raw.decode("utf-8") or "{}")
        except json.JSONDecodeError:
            self.send_error(400, "Invalid JSON")
            return

        fold = payload.get("fold")
        if fold is None:
            self.send_error(400, "Missing 'fold' payload")
            return

        title = str(payload.get("title") or "pattern")
        filename = f"{_safe_stem(title)}.fold"

        DATA_DIR.mkdir(parents=True, exist_ok=True)
        out_path = DATA_DIR / filename
        with out_path.open("w", encoding="utf-8") as handle:
            json.dump(fold, handle, indent=2, ensure_ascii=True)

        response = {
            "saved": True,
            "filename": filename,
            "path": str(out_path),
        }
        body = json.dumps(response).encode("utf-8")

        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def main() -> int:
    parser = argparse.ArgumentParser(description="Origami web server")
    parser.add_argument("--port", type=int, default=8000)
    args = parser.parse_args()

    if not WEB_DIR.is_dir():
        raise SystemExit(f"Web directory not found: {WEB_DIR}")

    server = ThreadingHTTPServer(("", args.port), OrigamiHandler)
    print(f"Serving {WEB_DIR} at http://localhost:{args.port}")
    print(f"Export endpoint: http://localhost:{args.port}/export-fold")
    server.serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

