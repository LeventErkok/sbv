#!/usr/bin/env python3
"""Run the paper's semantic checks and keep a complete, dated execution log."""
from datetime import datetime, timezone
from pathlib import Path
import shlex
import subprocess
import sys
import time

paper = Path(__file__).resolve().parent
repo = paper.parent
build = paper / "build"
build.mkdir(exist_ok=True)
results = paper / "results"
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

    record("SBV experience-report companion validation")
    record("UTC: " + datetime.now(timezone.utc).isoformat())
    record("Scope: paper examples only; not the full repository test suite.")
    for command in [["git", "rev-parse", "HEAD"], ["ghc", "--numeric-version"],
                    ["cabal", "--numeric-version"], ["z3", "--version"],
                    ["cvc5", "--version"], ["cc", "--version"]]:
        run(command)
    run([sys.executable, "paper/prepare.py"])
    run(["cabal", "exec", "--offline", "--", "ghc", "-O0", "-Wall", "-Werror",
         "-i", "-ipaper/examples", "-package", "sbv", "-outputdir", "paper/build",
         "-o", "paper/build/paper-examples", "paper/examples/PaperExamples.hs"])
    run(["paper/build/paper-examples"])
    run(["paper/build/paper-examples", "--const-fold"])
    (build / "c").mkdir(exist_ok=True)
    run(["paper/build/paper-examples", "--generate", "paper/build/c"])
    run(["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
         "-fsanitize=undefined", "-fno-sanitize-recover=all", "-Ipaper/build/c",
         "paper/build/c/sat_add.c", "paper/examples/adder-check.c",
         "-o", "paper/build/adder-check"])
    run(["paper/build/adder-check"])
    record("\nVALIDATION PASSED: seven small Haskell checks, the existing constant-folding")
    record("proof, and exhaustive generated-C checking. Timings are single-run diagnostics,")
    record("not benchmark measurements. No full-suite or cross-solver claim is made.")
