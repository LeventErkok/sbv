#!/usr/bin/env python3
"""Fetch the pinned, unmodified official JFP class for the manuscript build."""
from hashlib import sha256
from io import BytesIO
from pathlib import Path
from urllib.request import urlopen
from zipfile import ZipFile

URL = "https://jfp.episciences.org/jfp/resources/jfp_epi_1.2.zip"
ARCHIVE_SHA256 = "6255daa991d5836bfbd8313c1a31a7f5f1936a668791ad5db8ba130aa9ad4203"
CLASS_SHA256 = "310c2b8ef8c6dc8af207ba287ed1fda805fe36bfeb59c6c55f82f1ab556647b4"


def main():
    root = Path(__file__).resolve().parent
    target = root / "jfp-epi.cls"
    if target.exists():
        if sha256(target.read_bytes()).hexdigest() != CLASS_SHA256:
            raise SystemExit("jfp-epi.cls differs from the pinned official class; inspect it before replacing it.")
        print("Official JFP class v1.2 verified (cached).")
        return
    archive = root / "build/jfp-format/jfp_epi_1.2.zip"
    archive.parent.mkdir(parents=True, exist_ok=True)
    if archive.exists():
        data = archive.read_bytes()
    else:
        print("Fetching official JFP class v1.2...", flush=True)
        with urlopen(URL, timeout=120) as response:
            data = response.read()
    if sha256(data).hexdigest() != ARCHIVE_SHA256:
        raise SystemExit("JFP archive checksum mismatch; inspect the upstream distribution before updating the pin.")
    with ZipFile(BytesIO(data)) as bundle:
        cls = bundle.read("jfp-epi/jfp-epi.cls")
    if sha256(cls).hexdigest() != CLASS_SHA256:
        raise SystemExit("JFP class checksum mismatch.")
    archive.write_bytes(data)
    target.write_bytes(cls)
    print("Installed unmodified official JFP class v1.2.")


if __name__ == "__main__":
    main()
