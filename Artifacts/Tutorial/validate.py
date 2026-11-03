#!/usr/bin/env python3
"""Run the tutorial's checks and keep a complete, dated execution log."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import shlex
import subprocess
import sys
import time

tutorial = Path(__file__).resolve().parent
repo = tutorial.parents[1]
build = tutorial / "build"
build.mkdir(exist_ok=True)
results = tutorial / "results"
results.mkdir(exist_ok=True)
log_path = results / "validation.txt"

with log_path.open("w") as log:
    def record(text):
        print(text, flush=True)
        log.write(text + "\n")
        log.flush()

    def run(args, timeout=180):
        record("\n$ " + shlex.join(map(str, args)))
        start = time.monotonic()
        try:
            result = subprocess.run(args, cwd=repo, text=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired as error:
            output = error.stdout or b""
            if isinstance(output, bytes):
                output = output.decode(errors="replace")
            record(output)
            record(f"TIMEOUT after {timeout}s; validation incomplete")
            raise SystemExit(1)
        record(result.stdout.rstrip())
        record(f"Exit status: {result.returncode}; elapsed: {time.monotonic() - start:.2f}s")
        if result.returncode:
            record("VALIDATION FAILED")
            raise SystemExit(result.returncode)
        return result.stdout

    record("SBV tutorial companion validation")
    record("UTC: " + datetime.now(timezone.utc).isoformat())
    record("Scope: tutorial examples only; not the full repository test suite.")
    for command in [["git", "rev-parse", "HEAD"], ["ghc", "--numeric-version"],
                    ["cabal", "--numeric-version"], ["z3", "--version"],
                    ["cvc5", "--version"], ["cc", "--version"]]:
        run(command)
    record("\nLibrary source changes relative to the recorded revision (empty means clean):")
    run(["git", "status", "--short", "--", "Data", "Documentation", "sbv.cabal"])
    record("\nSHA-256 of validation inputs:")
    for path in [tutorial / "examples/TutorialExamples.hs", tutorial / "examples/adder-check.c",
                 tutorial / "validate.py", tutorial / "prepare.py", repo / "sbv.cabal",
                 repo / "Documentation/SBV/Examples/TP/Lists.hs",
                 repo / "Documentation/SBV/Examples/TP/TautologyChecker.hs"]:
        record(f"{sha256(path.read_bytes()).hexdigest()}  {path.relative_to(repo)}")
    record("\nLibrary package description:\n" + "\n".join(
        line for line in (repo / "sbv.cabal").read_text().splitlines()
        if line.startswith(("Name ", "Version "))))
    run([sys.executable, tutorial / "prepare.py"])
    run(["cabal", "exec", "--offline", "--", "ghc", "-O0", "-Wall", "-Werror",
         "-i", "-i" + str(tutorial / "examples"), "-package", "sbv",
         "-outputdir", build, "-o", build / "tutorial-examples",
         tutorial / "examples/TutorialExamples.hs"])
    output = run([build / "tutorial-examples"])
    if "*** Failed to prove revWeak.2." not in output:
        record("VALIDATION FAILED: expected failure at reversal step 2 was not observed")
        raise SystemExit(1)
    run([build / "tutorial-examples", "--tautology"])
    (build / "c").mkdir(exist_ok=True)
    run([build / "tutorial-examples", "--generate", build / "c"])
    run(["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
         "-fsanitize=undefined", "-fno-sanitize-recover=all", "-I" + str(build / "c"),
         build / "c/sat_add.c", tutorial / "examples/adder-check.c",
         "-o", build / "adder-check"])
    run([build / "adder-check"])
    record("\nVALIDATION PASSED: all tutorial checks (including exercise solutions), the")
    record("tautology checker's soundness and completeness proofs, and exhaustive")
    record("generated-C checking. Timings are single-run diagnostics, not benchmarks.")
