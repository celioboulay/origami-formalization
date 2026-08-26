#!/usr/bin/env python3
import argparse
import json
import shutil
import subprocess
import threading
import uuid
from datetime import datetime
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

from origami_api import OrigamiAPI

ROOT_DIR = Path(__file__).resolve().parent
WEB_DIR = ROOT_DIR / "origami-sim" / "web"
LEAN_OUTPUT = ROOT_DIR / "Origami" / "generated" / "construction.lean"

JOBS = {}
JOBS_LOCK = threading.Lock()
ORIGAMI_API = OrigamiAPI(lean_output_path=LEAN_OUTPUT)


class OrigamiHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(WEB_DIR), **kwargs)

    def do_POST(self):
        _log(f"POST {self.path}")
        if self.path == "/add-axiom":
            self._handle_add_axiom()
            return
        if self.path == "/add-reference":
            self._handle_add_reference()
            return
        if self.path == "/undo-last":
            self._handle_undo_last()
            return
        if self.path == "/clear-axioms":
            self._handle_clear_axioms()
            return
        if self.path == "/build-lean":
            self._handle_build_lean()
            return
        self.send_error(404, "Not Found")

    def do_GET(self):
        _log(f"GET {self.path}")
        if self.path.startswith("/build-lean/status"):
            self._handle_build_lean_status()
            return
        if self.path == "/axioms":
            self._handle_get_axioms()
            return
        super().do_GET()

    def _handle_add_axiom(self):
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length) if length > 0 else b""
        try:
            payload = json.loads(raw.decode("utf-8") or "{}")
        except json.JSONDecodeError:
            self.send_error(400, "Invalid JSON")
            return

        axiom_type = payload.get("type")
        params = payload.get("params")
        produced = payload.get("produced")
        if axiom_type is None or params is None:
            self.send_error(400, "Missing 'type' or 'params'")
            return

        try:
            axiom_summary = ORIGAMI_API.add_axiom(axiom_type, params, produced)
        except ValueError as e:
            self.send_error(400, str(e))
            return

        _log(f"Axiom {axiom_type} added (stack size {len(ORIGAMI_API.axioms)})")
        self._send_json(
            200,
            {
                "status": "axiom added",
                "axiom": axiom_summary,
                "stack": ORIGAMI_API.describe_stack(),
            },
        )

    def _handle_add_reference(self):
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length) if length > 0 else b""
        try:
            payload = json.loads(raw.decode("utf-8") or "{}")
        except json.JSONDecodeError:
            self.send_error(400, "Invalid JSON")
            return

        axiom_type = payload.get("type")
        params = payload.get("params")
        produced = payload.get("produced")
        if axiom_type is None or params is None or produced is None:
            self.send_error(400, "Missing 'type', 'params', or 'produced'")
            return

        try:
            reference_summary = ORIGAMI_API.add_reference(axiom_type, params, produced)
        except ValueError as e:
            self.send_error(400, str(e))
            return

        _log(f"Reference axiom {axiom_type} added (references size {len(ORIGAMI_API.references)})")
        self._send_json(
            200,
            {
                "status": "reference added",
                "reference": reference_summary,
                "stack": ORIGAMI_API.describe_stack(),
            },
        )

    def _handle_undo_last(self):
        kind = ORIGAMI_API.undo_last()
        self._send_json(
            200,
            {
                "status": "undone" if kind else "empty",
                "kind": kind,
                "stack": ORIGAMI_API.describe_stack(),
            },
        )

    def _handle_clear_axioms(self):
        ORIGAMI_API.clear()
        self._send_json(200, {"status": "cleared", "stack": ORIGAMI_API.describe_stack()})

    def _handle_get_axioms(self):
        self._send_json(200, ORIGAMI_API.describe_stack())

    def _handle_build_lean(self):
        # The Lean File is kept in sync continuously as axioms are
        # stacked (see OrigamiAPI._sync_lean_file); building just reads
        # and evaluates whatever is already on disk.
        _log(f"Building Lean file at {LEAN_OUTPUT}")

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
            args=(job_id, LEAN_OUTPUT),
            daemon=True,
        )
        thread.start()

        self._send_json(200, {"job_id": job_id})

    def _handle_build_lean_status(self):
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


def _run_lean_job(job_id: str, lean_file: Path) -> None:
    _update_job(job_id, status="running", step="compile")
    lake = shutil.which("lake")
    if not lake:
        _update_job(job_id, status="done", step="compile", error="lake not found in PATH")
        return

    compile_run = _run_command(
        [lake, "env", "lean", str(lean_file)],
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
    _log(f"Axiom endpoints: /add-axiom, /add-reference, /undo-last, /clear-axioms (POST), /axioms (GET)")
    _log(f"Build endpoints: /build-lean (POST), /build-lean/status (GET)")
    server.serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
