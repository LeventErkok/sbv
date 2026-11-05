"""Locate the pinned SBV sources fetched by this companion's Cabal project."""
import json
import subprocess


def sbv_source(root):
    plan_path = root / "dist-newstyle/cache/plan.json"
    if not plan_path.exists():
        raise SystemExit("Run 'cabal build tutorial-examples' before extracting or validating listings.")
    plan = json.loads(plan_path.read_text())
    packages = [p for p in plan["install-plan"] if p["pkg-name"] == "sbv"]
    if len(packages) != 1:
        raise SystemExit("Expected exactly one SBV dependency in the Cabal build plan.")
    package = packages[0]
    revision = package["pkg-src"]["source-repo"]["tag"]
    for cabal_file in (root / "dist-newstyle/src").glob("*/sbv.cabal"):
        source = cabal_file.parent.resolve()
        result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=source,
                                capture_output=True, text=True, check=False)
        if result.returncode == 0 and result.stdout.strip() == revision:
            return source, package
    raise SystemExit("Pinned SBV source checkout not found; run 'cabal build tutorial-examples'.")
