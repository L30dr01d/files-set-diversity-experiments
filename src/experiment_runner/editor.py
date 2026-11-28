"""Local cluster editor. The server reads the repository and validates downloads."""

import json
import webbrowser
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

from .cli import matrix_payload
from .config import FASTR_ALGORITHMS, KNOWN_TYPES, parse_config, validate_paths


def editor_server(root: Path) -> HTTPServer:
    class Handler(BaseHTTPRequestHandler):
        def reply(self, status, mime, content):
            self.send_response(status)
            self.send_header("Content-Type", mime)
            self.send_header("Content-Length", str(len(content)))
            self.end_headers()
            self.wfile.write(content)

        def do_GET(self):
            if self.path == "/":
                self.reply(
                    200,
                    "text/html; charset=utf-8",
                    Path(__file__).with_name("editor.html").read_bytes(),
                )
            elif self.path == "/config":
                self.reply(
                    200, "application/json", (root / "experiments.json").read_bytes()
                )
            elif self.path == "/catalog":
                catalog = dict(
                    datasets=sorted(
                        p.name
                        for p in (root / "datasets").iterdir()
                        if p.is_dir() and not p.name.startswith(".")
                    ),
                    tools=sorted(
                        p.name for p in (root / "tools").glob("*-measure") if p.is_dir()
                    ),
                    algorithms=FASTR_ALGORITHMS,
                    types=sorted(KNOWN_TYPES),
                )
                self.reply(200, "application/json", json.dumps(catalog).encode())
            else:
                self.send_error(404)

        def do_POST(self):
            if self.path != "/validate":
                self.send_error(404)
                return
            try:
                size = int(self.headers.get("Content-Length", "0"))
                if not 0 < size <= 8_000_000:
                    raise ValueError("invalid config size")
                entries = parse_config(json.loads(self.rfile.read(size)))
                validate_paths(root, entries)
                matrix_payload(entries)
            except (ValueError, TypeError) as exc:
                self.reply(400, "text/plain; charset=utf-8", str(exc).encode())
                return
            self.reply(200, "text/plain", b"OK")

    return HTTPServer(("127.0.0.1", 0), Handler)


def serve(root: Path) -> None:
    with editor_server(root) as server:
        url = f"http://127.0.0.1:{server.server_port}/"
        print(url, flush=True)
        webbrowser.open(url)
        server.serve_forever()
