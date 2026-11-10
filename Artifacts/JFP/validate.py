#!/usr/bin/env python3
"""Run the tutorial's checks and keep a complete, dated execution log."""
import ast
import re
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

    record("SBV JFP tutorial companion validation")
    record("UTC: " + datetime.now(timezone.utc).isoformat())
    record("Scope: tutorial examples only; not the full repository test suite.")
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=tutorial,
                              capture_output=True, text=True, check=False)
    record("Companion repository revision: " + revision.stdout.strip()
           if revision.returncode == 0 else "Companion directory is not a Git checkout; input hashes identify its sources.")
    if revision.returncode == 0:
        record("Companion working-tree status (input hashes below identify this draft):")
        run(["git", "status", "--short", "--", "."])
    for command in [["ghc", "--numeric-version"],
                    ["cabal", "--numeric-version"], ["z3", "--version"],
                    ["cvc5", "--version"], ["cc", "--version"]]:
        run(command)
    run(["cabal", "build", "--offline", "-fstrict", "tutorial-examples"], timeout=900)
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
        (tutorial, "", ["examples/TutorialExamples.hs", "examples/ExpandedExamples.hs", "examples/adder-check.c",
                        "validate.py", "prepare.py", "companion.py", "sbv-tutorial.cabal",
                        "cabal.project", "cabal.project.freeze", "jfp_format.py",
                        "sbv-tutorial.tex", "references.bib", "Makefile", "LICENSE"]),
        (repo, "SBV/", ["sbv.cabal", "Data/SBV/TP/TP.hs", "Documentation/SBV/Examples/TP/Lists.hs",
                        "Documentation/SBV/Examples/TP/TautologyChecker.hs",
                        "Documentation/SBV/Examples/TP/Basics.hs",
                        "Documentation/SBV/Examples/ProofTools/BMC.hs",
                        "Documentation/SBV/Examples/ProofTools/Strengthen.hs",
                        "Documentation/SBV/Examples/WeakestPreconditions/Basics.hs",
                        "Documentation/SBV/Examples/TP/BinarySearch.hs",
                        "Documentation/SBV/Examples/BitPrecise/BrokenSearch.hs",
                        "Documentation/SBV/Examples/BitPrecise/Adders.hs",
                        "Data/SBV/Set.hs", "Data/SBV/RegExp.hs", "Data/SBV/Rational.hs",
                        "Data/SBV/TP/Utils.hs", "Data/SBV/Client.hs",
                        "Data/SBV/Core/Model.hs", "Data/SBV/Maybe.hs", "Data/SBV/List.hs",
                        "Data/SBV/Provers/Prover.hs", "Data/SBV/Tools/Overflow.hs"]),
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
    run([executable, "--expanded"])
    run([executable, "--synthesis"])
    failures = run([executable, "--tp-failures"])
    def failed_obligation(name, obligation, *, assumptions=False):
        block = failures.split("BEGIN " + name + "\n", 1)[1].split("END " + name, 1)[0]
        kind = "assumptions for " if assumptions else ""
        if (f"*** Failed to prove {kind}{obligation}." not in block or
                "Falsifiable. Counter-example:" not in block):
            raise SystemExit(f"Expected a refuting model for {name}, not just an exception")
        return block

    length_model = failed_obligation("badLengthProof", "badLengthProof")
    xs = ast.literal_eval(re.search(r"xs\s*=\s*(\[[^\n]*\])\s*::", length_model)[1])
    imp = int(re.search(r"imp\s*=\s*(-?\d+)\s*::", length_model)[1])
    spec = int(re.search(r"spec\s*=\s*(-?\d+)\s*::", length_model)[1])
    if not (len(xs) > 5 and 42 in xs and imp == 42 and spec == len(xs) and imp != spec):
        raise SystemExit("TP length model fails independent concrete replay")

    step_model = failed_obligation("badCalculation", "badCalculation.1")
    n = int(re.search(r"\bn\s*=\s*(-?\d+)\s*::", step_model)[1])
    if not (n + n != 2*n + 1 and n + n == 2*n):
        raise SystemExit("TP step model does not distinguish the step from its theorem")

    hint_model = failed_obligation("badJustification", "badJustification.1", assumptions=True)
    n = int(re.search(r"\bn\s*=\s*(-?\d+)\s*::", hint_model)[1])
    if not (n < 0 and n + n == 2*n):
        raise SystemExit("TP hint model does not refute the justification while satisfying the equality")

    function_model = failed_obligation("forallDisjunctionNot", "forallDisjunctionNot")
    def predicate(name):
        rows = re.findall(r"^\s*" + name + r"\s+(-?\d+|_)\s*=\s*(True|False)\s*$",
                          function_model, re.M)
        values = {key: value == "True" for key, value in rows}
        if "_" not in values:
            raise SystemExit("Function model has no default value")
        return values
    p, q = predicate("p"), predicate("q")
    # The union of explicit arguments plus the default partitions the entire
    # integer domain for these finite function interpretations.
    regions = set(p) | set(q)
    pv = [p.get(k, p["_"]) for k in regions]
    qv = [q.get(k, q["_"]) for k in regions]
    if not (all(a or b for a, b in zip(pv, qv)) and not all(pv) and not all(qv)):
        raise SystemExit("Function model does not refute the quantified equivalence")
    record("PASS TP diagnostics: replayed concrete, intermediate-step, and function models")
    run([executable, "--binary-search"])
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
    record("solutions and midpoint checks), all expanded semantic-domain and query examples,")
    record("counterexample-guided synthesis and its independent oracles, the strengthened binary-search TP proof,")
    record("binary-search concrete oracles, TP counterexample replay, verbose diagnostics and SMT-LIB transcript replay, the")
    record("tautology checker's truth-table checks, soundness and completeness proofs, and exhaustive")
    record("generated-C checking. Timings are single-run diagnostics, not benchmarks.")
