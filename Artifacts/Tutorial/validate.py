#!/usr/bin/env python3
"""Run the tutorial's checks and keep a complete, dated execution log."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import shlex
import subprocess
import sys
import time
from companion import sbv_source

tutorial = Path(__file__).resolve().parent
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

    def run(args, timeout=180, cwd=tutorial):
        record("\n$ " + shlex.join(map(str, args)))
        start = time.monotonic()
        try:
            result = subprocess.run(args, cwd=cwd, text=True,
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
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tutorial,
                              capture_output=True, text=True, check=False)
    record("Companion repository revision: " + revision.stdout.strip()
           if revision.returncode == 0 else "Companion directory is not a Git checkout; input hashes identify its sources.")
    for command in [["ghc", "--numeric-version"],
                    ["cabal", "--numeric-version"], ["z3", "--version"],
                    ["cvc5", "--version"], ["cc", "--version"]]:
        run(command)
    run(["cabal", "build", "--offline", "tutorial-examples"], timeout=900)
    repo, package = sbv_source(tutorial)
    record("\nSBV source revision: " + package["pkg-src"]["source-repo"]["tag"])
    record("SBV source package SHA-256: " + package["pkg-src-sha256"])
    record("Library source changes relative to that revision (empty means clean):")
    changes = run(["git", "status", "--short", "--", "Data", "Documentation", "sbv.cabal"], cwd=repo)
    if changes.strip():
        record("VALIDATION FAILED: the pinned SBV sources have local changes")
        raise SystemExit(1)
    record("\nSHA-256 of validation inputs:")
    for base, prefix, names in [
        (tutorial, "", ["examples/TutorialExamples.hs", "examples/adder-check.c",
                        "validate.py", "prepare.py", "companion.py", "sbv-tutorial.cabal",
                        "cabal.project", "cabal.project.freeze"]),
        (repo, "SBV/", ["sbv.cabal", "Documentation/SBV/Examples/TP/Lists.hs",
                        "Documentation/SBV/Examples/TP/TautologyChecker.hs"]),
    ]:
        for name in names:
            record(f"{sha256((base / name).read_bytes()).hexdigest()}  {prefix}{name}")
    record("\nLibrary package description:\n" + "\n".join(
        line for line in (repo / "sbv.cabal").read_text().splitlines()
        if line.startswith(("Name ", "Version "))))
    run([sys.executable, tutorial / "prepare.py"])
    executable = Path(run(["cabal", "list-bin", "tutorial-examples", "-v0"]).strip())
    output = run([executable])
    if "*** Failed to prove revWeak.2." not in output:
        record("VALIDATION FAILED: expected failure at reversal step 2 was not observed")
        raise SystemExit(1)
    run([executable, "--tautology"])
    transcript = build / "sat-add.smt2"
    run([executable, "--diagnostics", transcript])
    replay = run(["z3", transcript])
    if "unsat" not in replay.splitlines() or "(error" in replay:
        record("VALIDATION FAILED: solver transcript did not replay successfully")
        raise SystemExit(1)
    (build / "c").mkdir(exist_ok=True)
    run([executable, "--generate", build / "c"])
    run(["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
         "-fsanitize=undefined", "-fno-sanitize-recover=all", "-I" + str(build / "c"),
         build / "c/sat_add.c", tutorial / "examples/adder-check.c",
         "-o", build / "adder-check"])
    run([build / "adder-check"])
    record("\nVALIDATION PASSED: all tutorial checks (including random tests and exercise")
    record("solutions), verbose diagnostics and SMT-LIB transcript replay, the")
    record("tautology checker's soundness and completeness proofs, and exhaustive")
    record("generated-C checking. Timings are single-run diagnostics, not benchmarks.")
