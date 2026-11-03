#!/usr/bin/env python3
"""Extract the tutorial's listings from checked Haskell sources.

Two sources are used:
  * examples/TutorialExamples.hs, delimited by '-- BEGIN name' / '-- END name';
  * declarations quoted verbatim from SBV's own documentation modules, taken
    from the declaration's first line up to the next top-level line.
Every \\snippet{name} or \\libsnippet{name} used by the manuscript must resolve to an extracted file.
"""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
repo = root.parents[1]
destination = root / "build" / "snippets"
destination.mkdir(parents=True, exist_ok=True)
for stale in destination.glob("*.hs"):
    stale.unlink()

snippets = {}

companion = (root / "examples" / "TutorialExamples.hs").read_text()
for name, body in re.findall(r"^-- BEGIN (\w+)\n(.*?)^-- END \1$", companion, re.M | re.S):
    snippets[name] = body

# (snippet name, library module, regex matching the declaration's first line)
library = [
    ("tautFormula",      "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^data Formula "),
    ("tautSoundness",    "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^soundness :: "),
    ("tautCompleteness", "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^completeness :: "),
]
for name, module, start in library:
    lines = (repo / module).read_text().splitlines()
    first = next((i for i, l in enumerate(lines) if re.match(start, l)), None)
    if first is None:
        raise SystemExit(f"{module}: no declaration matching {start!r}")
    last = first + 1
    while last < len(lines) and (not lines[last].strip() or lines[last][0].isspace()
                                 or lines[last].startswith(lines[first].split()[0] + " ")):
        last += 1
    while not lines[last - 1].strip():
        last -= 1
    snippets[name] = "\n".join(lines[first:last]) + "\n"

used = set(re.findall(r"\\(?:lib)?snippet\{(\w+)\}", (root / "sbv-tutorial.tex").read_text()))
missing = sorted(used - snippets.keys())
if missing:
    raise SystemExit(f"Manuscript uses listings with no source: {', '.join(missing)}")

for name, body in snippets.items():
    (destination / f"{name}.hs").write_text(body)
print(f"Extracted {len(snippets)} listings ({len(used)} used by the manuscript)")
