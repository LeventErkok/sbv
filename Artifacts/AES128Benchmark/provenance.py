#!/usr/bin/env python3
"""Record source revisions, input hashes, and non-identifying host metadata."""
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys

root = Path(__file__).resolve().parent
def command(args, cwd=root):
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.DEVNULL).strip()

path = root / "results/provenance.json"
metadata = json.loads(path.read_text()) if path.exists() else {}
urls = {"benchmark": "https://github.com/google/benchmark",
        "bearssl": "https://www.bearssl.org/git/BearSSL",
        "tiny-AES-c": "https://github.com/kokke/tiny-AES-c"}
if "sources" not in metadata:
    metadata["sources"] = {name: {"url": url, "commit": command(
        ["git", "rev-parse", "HEAD"], root / "vendor" / name)}
        for name, url in urls.items()}
if "sbv_commit" not in metadata or "--record-generation" in sys.argv:
    metadata["sbv_commit"] = command(["git", "rev-parse", "HEAD"])
    # Tracked modifications could change the code generator without changing HEAD.
    # Untracked files and this directory itself are excluded.
    dirty = [line[3:] for line in command(
        ["git", "status", "--porcelain", "--untracked-files=no"]).splitlines()
        if not line[3:].startswith("Artifacts/AES128Benchmark/")]
    metadata["sbv_tree_dirty"] = bool(dirty)
    metadata["sbv_dirty_paths"] = dirty
    metadata["sbv_source_sha256"] = hashlib.sha256(
        (root.parents[1] / "Documentation/SBV/Examples/Crypto/AES.hs").read_bytes()).hexdigest()

machine = platform.machine()
if platform.system() == "Darwin":
    try:
        hardware = command(["system_profiler", "SPHardwareDataType"])
        wanted = ("Model Name:", "Model Identifier:", "Chip:", "Total Number of Cores:", "Memory:")
        # Intentionally omit serial numbers and other device identifiers.
        machine = "; ".join(line.strip() for line in hardware.splitlines()
                            if line.strip().startswith(wanted))
    except subprocess.CalledProcessError:
        pass
metadata["machine"] = machine
metadata["os"] = platform.platform()
cache = (root / "build/CMakeCache.txt")
compiler = "cc"
if cache.exists():
    for line in cache.read_text().splitlines():
        if line.startswith("CMAKE_C_COMPILER:FILEPATH="):
            compiler = line.split("=", 1)[1]
        if line.startswith("OPENSSL_CRYPTO_LIBRARY:FILEPATH="):
            library = Path(line.split("=", 1)[1]).resolve()
            metadata["openssl_library"] = {"path": str(library),
                "sha256": hashlib.sha256(library.read_bytes()).hexdigest()}
metadata["compiler"] = command([compiler, "--version"])
metadata["build_flags"] = "-O3 -DNDEBUG; no LTO; no explicit architecture flags"
files = []
for dirname in ("generated", "vendor"):
    files.extend(p for p in (root / dirname).rglob("*") if p.is_file()
                 and ".git" not in p.relative_to(root).parts)
files.extend(root / name for name in ("benchmark.cpp", "CMakeLists.txt", "Generate.hs",
                                     "run.sh", "report.py", "provenance.py"))
metadata["sha256"] = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(files)}
# The vendored trees are subsets of the upstream commits above. Every remaining file
# must still match the hash recorded when the full trees were first vendored.
original = metadata.get("vendor_original_sha256", {})
changed = sorted(name for name, digest in metadata["sha256"].items()
                 if name.startswith("vendor/") and original.get(name) != digest)
if changed:
    raise SystemExit("Vendored files differ from their original recorded hashes: " + ", ".join(changed))
metadata["vendor_subset"] = {"files_kept": sum(n.startswith("vendor/") for n in metadata["sha256"]),
                             "files_originally_vendored": len(original),
                             "kept_files_unmodified": True}
path.write_text(json.dumps(metadata, indent=2) + "\n")
