#!/usr/bin/env python3
import argparse
import json
import re
import shutil
import subprocess
import threading
import uuid
import sys
from datetime import datetime
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

ROOT_DIR = Path(__file__).resolve().parent
WEB_DIR = ROOT_DIR / "origami-sim" / "web"
DATA_DIR = ROOT_DIR / "data"
LEAN_SCRIPT = ROOT_DIR / "Origami" / "FOLD_verification" / "FOLD_2_lean.py"
LEAN_OUTPUT = ROOT_DIR / "Origami" / "FOLD_verification" / "parsed.lean"

JOBS = {}
JOBS_LOCK = threading.Lock()


def _safe_stem(value: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9._-]+", "_", value).strip("._")
    return cleaned or "pattern"


class OrigamiHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(WEB_DIR), **kwargs)

    def do_POST(self):
        _log(f"POST {self.path}")
        if self.path == "/export-fold":
            self._handle_export_fold()
            return
        if self.path == "/run-lean":
            self._handle_run_lean()
            return
        self.send_error(404, "Not Found")

    def do_GET(self):
        _log(f"GET {self.path}")
        if self.path.startswith("/run-lean/status"):
            self._handle_run_lean_status()
            return
        super().do_GET()

    def _handle_export_fold(self):
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
        _log(f"Saved FOLD to {out_path}")

        response = {
            "saved": True,
            "filename": filename,
            "path": str(out_path),
        }
        self._send_json(200, response)

    def _handle_run_lean(self):
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length) if length > 0 else b""
        try:
            payload = json.loads(raw.decode("utf-8") or "{}")
        except json.JSONDecodeError:
            self.send_error(400, "Invalid JSON")
            return

        filename = payload.get("filename")
        if not filename:
            self.send_error(400, "Missing 'filename'")
            return

        fold_path = DATA_DIR / filename
        if not fold_path.is_file():
            self.send_error(404, f"FOLD file not found: {filename}")
            return
        _log(f"Lean job requested for {fold_path}")

        job_id = uuid.uuid4().hex
        with JOBS_LOCK:
            JOBS[job_id] = {
                "status": "queued",
                "step": "queued",
                "success": False,
                "log": "",
                "error": "",
            }

        thread = threading.Thread(
            target=_run_lean_job,
            args=(job_id, fold_path),
            daemon=True,
        )
        thread.start()

        self._send_json(200, {"job_id": job_id})

    def _handle_run_lean_status(self):
        parsed = urlparse(self.path)
        params = parse_qs(parsed.query)
        job_id = params.get("job_id", [""])[0]
        if not job_id:
            self.send_error(400, "Missing job_id")
            return

        with JOBS_LOCK:
            job = JOBS.get(job_id)
        if not job:
            self.send_error(404, "Job not found")
            return

        self._send_json(200, job)

    def _send_json(self, status: int, payload: dict) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def _update_job(job_id: str, **fields: str) -> None:
    with JOBS_LOCK:
        job = JOBS.get(job_id)
        if not job:
            return
        job.update(fields)
    if fields:
        _log(f"Job {job_id}: {fields}")


def _run_command(cmd, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=False,
    )


def _run_lean_job(job_id: str, fold_path: Path) -> None:
    _update_job(job_id, status="running", step="convert", log="", error="")

    if not LEAN_SCRIPT.is_file():
        _update_job(job_id, status="done", step="convert", error="Lean script missing")
        return

    convert = _run_command(
        [
            sys.executable,
            str(LEAN_SCRIPT),
            "--input",
            str(fold_path),
            "--output",
            str(LEAN_OUTPUT),
        ],
        cwd=ROOT_DIR,
    )
    if convert.returncode != 0:
        _update_job(
            job_id,
            status="done",
            step="convert",
            error=convert.stderr.strip() or convert.stdout.strip() or "Conversion failed",
            log=(convert.stdout + convert.stderr).strip(),
        )
        return

    _update_job(job_id, step="compile")
    lake = shutil.which("lake")
    if not lake:
        _update_job(job_id, status="done", step="compile", error="lake not found in PATH")
        return

    compile_run = _run_command(
        [lake, "env", "lean", str(LEAN_OUTPUT)],
        cwd=ROOT_DIR,
    )
    if compile_run.returncode != 0:
        _update_job(
            job_id,
            status="done",
            step="compile",
            error=compile_run.stderr.strip() or compile_run.stdout.strip() or "Lean compile failed",
            log=(compile_run.stdout + compile_run.stderr).strip(),
        )
        return

    _update_job(job_id, status="done", step="done", success=True, log="Lean compile succeeded")


def _log(message: str) -> None:
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{timestamp}] {message}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Origami web server")
    parser.add_argument("--port", type=int, default=8000)
    args = parser.parse_args()

    if not WEB_DIR.is_dir():
        raise SystemExit(f"Web directory not found: {WEB_DIR}")

    server = ThreadingHTTPServer(("", args.port), OrigamiHandler)
    _log(f"Serving {WEB_DIR} at http://localhost:{args.port}")
    _log(f"Export endpoint: http://localhost:{args.port}/export-fold")
    _log(f"Lean endpoint: http://localhost:{args.port}/run-lean")
    server.serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

