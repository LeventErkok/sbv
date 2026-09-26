#!/usr/bin/env python3
"""Extract the paper's listings from the executable Haskell examples."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
destination = root / "build" / "snippets"
destination.mkdir(parents=True, exist_ok=True)
source = (root / "examples" / "PaperExamples.hs").read_text()
blocks = re.findall(r"^-- BEGIN (\w+)\n(.*?)^-- END \1$", source, re.M | re.S)
if len(blocks) != 5:
    raise SystemExit(f"Expected five source listings; found {len(blocks)}")
for name, body in blocks:
    (destination / f"{name}.hs").write_text(body)
print(f"Extracted {len(blocks)} executable listings")
