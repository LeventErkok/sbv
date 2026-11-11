#!/usr/bin/env python3
"""Remove host identifiers from saved results before they are committed.

Google Benchmark records the machine's host name in its JSON context, and build logs
contain absolute paths that include a user name. The hardware description kept in
provenance.json already omits serial numbers and device identifiers.
"""
import json
from pathlib import Path

root = Path(__file__).resolve().parent
for path in root.glob("results/**/*.json"):
    data = json.loads(path.read_text())
    context = data.get("context") if isinstance(data, dict) else None
    if context and "host_name" in context:
        context["host_name"] = "(removed)"
        path.write_text(json.dumps(data, indent=2) + "\n")
placeholder = "<AES128Benchmark>"
for path in list(root.glob("results/**/*.log")) + list(root.glob("results/**/*.txt")):
    text = path.read_text()
    if str(root) in text:
        path.write_text(text.replace(str(root), placeholder))
