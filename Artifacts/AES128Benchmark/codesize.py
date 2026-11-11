#!/usr/bin/env python3
"""Measure the compiled size of each AES object used by the benchmark.

Sizes come from the object files CMake built (same flags as the timed code), so they
are machine code and read-only data, not source lines. Mach-O (`size -m`) and ELF
(`size -A`) outputs are understood.
"""
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parent
objects = root / "build/CMakeFiles/aes_impl.dir"
# (label, object path relative to the CMake object directory, source file, scope)
entries = [
    ("SBV encryption", "generated/aes128BlockEncrypt.c.o", "generated/aes128BlockEncrypt.c",
     "block encryption only"),
    ("SBV key schedule", "generated/aes128KeySchedule.c.o", "generated/aes128KeySchedule.c",
     "key expansion only (not timed)"),
    ("BearSSL aes_big", "vendor/bearssl/src/symcipher/aes_big_enc.c.o",
     "vendor/bearssl/src/symcipher/aes_big_enc.c", "block encryption only"),
    ("BearSSL key schedule", "vendor/bearssl/src/symcipher/aes_common.c.o",
     "vendor/bearssl/src/symcipher/aes_common.c", "key expansion and tables (not timed)"),
    ("tiny-AES-c", "vendor/tiny-AES-c/aes.c.o", "vendor/tiny-AES-c/aes.c",
     "encryption, decryption, and key expansion; not separable"),
]

def sizes(obj):
    out = subprocess.check_output(["size", "-m" if Path("/usr/bin/otool").exists() else "-A",
                                   str(obj)], text=True)
    code = const = 0
    for line in out.splitlines():
        macho = re.search(r"Section \(__TEXT, (__text|__const|__literal\d+)\):\s+(\d+)", line)
        elf = re.match(r"\.(text|rodata)(?:\.\S+)?\s+(\d+)", line)
        if macho:
            if macho.group(1) == "__text":
                code += int(macho.group(2))
            else:
                const += int(macho.group(2))
        elif elf:
            if elf.group(1) == "text":
                code += int(elf.group(2))
            else:
                const += int(elf.group(2))
    return code, const

rows = []
for label, obj, source, scope in entries:
    candidates = list(objects.glob(obj)) or list(objects.rglob(Path(obj).name))
    if not candidates:
        raise SystemExit(f"Object file not found for {label}; build first")
    code, const = sizes(candidates[0])
    lines = len((root / source).read_text().splitlines())
    rows.append(dict(implementation=label, scope=scope, code_bytes=code, constant_bytes=const,
                     total_bytes=code + const, source_lines=lines))
(root / "results/codesize.json").write_text(json.dumps(rows, indent=2) + "\n")
for r in rows:
    print(f'{r["implementation"]:<22} code {r["code_bytes"]:>6}  data {r["constant_bytes"]:>6}  '
          f'total {r["total_bytes"]:>6}  ({r["source_lines"]} source lines)')
