#!/usr/bin/env python3
"""Extract the tutorial's listings from checked Haskell sources.

Two sources are used:
  * examples/TutorialExamples.hs, delimited by '-- BEGIN name' / '-- END name';
  * declarations extracted from SBV's own documentation modules, taken
    from the declaration's first line up to the next top-level line; two long
    declarations are reindented with a non-whitespace identity check.
PAPER-ELIDE-BEGIN/END comments replace checked code with a printed summary.
Every \\snippet{name}, \\snippet*{name}, or \\libsnippet{name} must resolve to an extracted file.
"""
from pathlib import Path
import re
from companion import sbv_source

root = Path(__file__).resolve().parent
repo, _ = sbv_source(root)
destination = root / "build" / "snippets"
destination.mkdir(parents=True, exist_ok=True)
for stale in destination.glob("*.hs"):
    stale.unlink()

snippets = {}

def paper_listing(name, body):
    """Elide only explicitly marked spans, rejecting malformed markers."""
    output = []
    eliding = False
    for line in body.splitlines(keepends=True):
        start = re.fullmatch(r"(\s*)-- PAPER-ELIDE-BEGIN (.+)\n?", line)
        if start:
            if eliding:
                raise SystemExit(f"{name}: nested paper elision")
            output.append(start[1] + start[2] + "\n")
            eliding = True
        elif line.strip() == "-- PAPER-ELIDE-END":
            if not eliding:
                raise SystemExit(f"{name}: unmatched paper elision end")
            eliding = False
        elif not eliding:
            output.append(line)
    if eliding:
        raise SystemExit(f"{name}: unclosed paper elision")
    return "".join(output)

companion = (root / "examples" / "TutorialExamples.hs").read_text()
for name, body in re.findall(r"^-- BEGIN (\w+)\n(.*?)^-- END \1$", companion, re.M | re.S):
    snippets[name] = paper_listing(name, body)

# (snippet name, library module, regex matching the declaration's first line)
library = [
    ("binarySearch", "Documentation/SBV/Examples/TP/BinarySearch.hs", r"^bsearch :: "),
    ("tautNormalize",    "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^normalize :: "),
    ("tautEval",         "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^eval :: "),
    ("tautCheck",        "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^isTautology' :: "),
    ("tautTop",          "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^isTautology :: "),
    ("tautFormula",      "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^data Formula "),
    ("tautSoundness",    "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^soundness :: "),
    ("tautCompleteness", "Documentation/SBV/Examples/TP/TautologyChecker.hs", r"^completeness :: "),
]
# Compact whitespace in two long library declarations for the printed page.
# The extraction below verifies that no non-whitespace character has changed;
# these declarations contain no string literals with significant whitespace.
formatted_library = {
    "tautNormalize": r'''normalize :: SFormula -> SFormula
normalize = smtFunctionWithMeasure "normalize"
  ( \f -> tuple (ifComplexity f, ifDepth f)
  , [ measureLemma ifDepthNonNeg
    , measureLemma ifComplexityPos
    , measureLemmaWith z3 ifComplexitySmaller
    , measureLemmaWith z3 normalizePreservesComplexity
    ]
  ) $ \f -> [sCase| f of
    If (If p q r) left right ->
      normalize (sIf p (sIf q left right) (sIf r left right))
    If c left right -> sIf c (normalize left) (normalize right)
    _ -> f
  |]
''',
    "tautSoundness": r'''soundness :: TP (Proof (Forall "f" Formula
                    -> Forall "bindings" [Binding] -> SBool))
soundness = do
  tie <- recallWith cvc5 tautologyImpliesEval
  nrt <- recall normalizeRespectsTruth
  nc  <- recall normalizeCorrect
  calc "soundness"
    (\(Forall f) (Forall bindings) -> isTautology f .=> eval f bindings) $
    \f bindings -> [isTautology f]
      |- eval f bindings
      ?? nrt `at` (Inst @"f" f, Inst @"bs" bindings)
      =: eval (normalize f) bindings
      ?? nc `at` Inst @"f" f
      ?? tie `at` (Inst @"f" (normalize f),
                   Inst @"a" bindings, Inst @"b" [])
      =: sTrue
      =: qed
''',
}
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
    source = "\n".join(lines[first:last]) + "\n"
    rendered = formatted_library.get(name, source)
    if re.sub(r"\s+", "", source) != re.sub(r"\s+", "", rendered):
        raise SystemExit(f"{name}: formatted listing differs from the library source")
    snippets[name] = rendered

used = set(re.findall(r"\\(?:lib)?snippet\*?\{(\w+)\}", (root / "sbv-tutorial.tex").read_text()))
missing = sorted(used - snippets.keys())
if missing:
    raise SystemExit(f"Manuscript uses listings with no source: {', '.join(missing)}")

for name, body in snippets.items():
    (destination / f"{name}.hs").write_text(body)
print(f"Extracted {len(snippets)} listings ({len(used)} used by the manuscript)")
