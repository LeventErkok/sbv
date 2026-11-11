# AES128 encryption with a reused key

This standalone Google Benchmark harness compares SBV-generated C, BearSSL
`aes_big`, tiny-AES-c, and OpenSSL EVP (single-block and bulk calls). The three portable C implementations are compiled with the same
compiler and `-O3 -DNDEBUG`, without LTO. The C++ driver calls the C objects.

OpenSSL is a different kind of implementation: on this machine it uses the CPU's AES
instructions, so it is included as a hardware reference, not as a peer of the
portable table-based C. Read the SBV, BearSSL, and tiny-AES-c rows as one comparison and
the OpenSSL rows as another. The code-size table in the report records what the
portable implementations pay in space for their speed.

Open [report.html](report.html) for measured results and methodology.
Raw repetitions, validation output, source provenance, and a CSV summary are
under `results/`.

## Build and run

Requires CMake 3.20+, a C/C++17 toolchain, and Python 3. No network access or
Haskell installation is needed to use the included generated C and vendor sources.
OpenSSL 3 development headers and libcrypto must also be installed. CMake uses
`find_package(OpenSSL)`; pass `-DOPENSSL_ROOT_DIR=/path/to/openssl` to CMake if needed.
The measured library is Homebrew OpenSSL 3.6.3; its path and binary hash are recorded
in provenance, and runtime version, provider, build flags and CPU capabilities in JSON.

```sh
cd Artifacts/AES128Benchmark
bash run.sh
```

This replaces the saved measurements and HTML report. Before timing it waits until the
1-minute load average is below `MAX_LOAD` (default: a quarter of the logical CPUs, since the
timed code is single-threaded) for up to `WAIT_SECONDS` (default 900), then stops unless
`ALLOW_BUSY=1`. The threshold and starting load go to `results/run_config.json` and the report;
a desktop with background apps will not be idle, and the report says so. Results are scrubbed of the host name and absolute
paths (`scrub.py`). It uses a release build,
0.2 seconds warmup, at least 0.5 seconds per measurement, nine randomly
interleaved repetitions, and 16-byte, 1-KiB, and 16-KiB buffers. Allow roughly
two to three minutes after compilation. For validation alone after building:

```sh
build/aes128_benchmark --validate-only
```

## Workload

Key expansion, allocations, input generation, and validation are outside timing.
Each timed iteration encrypts independent plaintext blocks from a fixed input
buffer into a separate output buffer. No block depends on another block's
ciphertext. The expanded key stays fixed for the entire run.

The `SBV` row includes big-endian byte/word conversion. The other two portable
implementations have in-place byte APIs, so their adapters copy each 16-byte
input before encryption. This measures a common byte-input/byte-output workload,
including per-block calls and adaptation. The `SBV_native_words` row calls the same
generated function on pre-converted 32-bit words and isolates it from that adapter. There is no padding or chaining. OpenSSL uses AES-128-ECB through the default
provider with normal hardware dispatch enabled. `OpenSSL_EVP_block` makes one
EVP update per 16-byte block; `OpenSSL_EVP_bulk` makes one update per entire
buffer. Both reuse a context initialized before timing, including an untimed
first encryption to complete any lazy setup. EVP checks and dispatch overhead
are included. The installed OpenSSL library has its own build flags, recorded
in the results, and is not compiled with the portable C sources.

All four implementations (plus SBV's native-word path) pass the FIPS-197 Appendix C.1 known-answer vector, then agree on
1,024 deterministic pseudorandom key/plaintext pairs before any benchmark runs. OpenSSL bulk encryption and context reuse are
also checked against SBV at all three buffer sizes.
BearSSL's internal single-block function is linked directly from unmodified
upstream C; it is not a stable public API.

Report times use median thread CPU time per block. Raw JSON includes CPU and
wall time for every repetition. Larger buffers amortize harness overhead and
still invoke one encryption function per block except for OpenSSL bulk. Results reflect warm buffers on
this machine, without CPU affinity or frequency control. The three portable table-based
implementations do not establish constant-time security.

## Code size

`codesize.py` reads the compiled object files (same flags as the timed code) and records code
and read-only data bytes in `results/codesize.json`. SBV's generated block encryptor is larger than
BearSSL's: it has no round loop and four 1 KiB lookup tables plus a 256-byte S-box, where BearSSL keeps one table and
rotates. tiny-AES-c's object includes decryption and key expansion, so its size is an upper bound
for encryption alone. The benchmark does not vary table size or unrolling independently, so the
size/speed relationship is an observation about these three implementations, not an isolated cause.

## Regenerate SBV C from the repository checkout

From the repository root, using its Haskell/Cabal prerequisites:

```sh
cabal --logs-dir=Artifacts/AES128Benchmark/results/cabal-logs build lib:sbv
mkdir -p Artifacts/AES128Benchmark/build
cabal exec -- ghc -i -package sbv Artifacts/AES128Benchmark/Generate.hs \
  -outputdir Artifacts/AES128Benchmark/build \
  -o Artifacts/AES128Benchmark/build/generate
Artifacts/AES128Benchmark/build/generate
python3 Artifacts/AES128Benchmark/provenance.py --record-generation
```

At commit `64315b78d` (clean tracked tree) the regenerated files were byte-identical to the saved
ones; `results/provenance.json` records the commit, whether tracked files were modified, and that check.
`Generate.hs` uses the same components as `cgAESLibrary 128`, with automatic
overwrite enabled for the generated artifacts. Only the encryption and key
schedule objects are linked into the benchmark. Decryption sources and the
generated example driver remain available for inspection.

## Sources and licenses

`results/provenance.json` records pinned upstream commits and SHA-256 hashes of
the generated sources and benchmark inputs. Vendor sources are included so the
exact versions can be rebuilt offline. Only the files the build reads are kept
(102 of the 707 originally vendored); each kept file is verified against the hash
recorded when the full trees were vendored, so none has been modified. Original
licenses are retained:

- Google Benchmark: `vendor/benchmark/LICENSE` (Apache-2.0).
- BearSSL: `vendor/bearssl/LICENSE.txt` (MIT).
- tiny-AES-c: `vendor/tiny-AES-c/unlicense.txt` (Unlicense).
- SBV: repository `LICENSE` (BSD-3-Clause).

`run.sh` updates current machine/compiler metadata and hashes while preserving
the original source revision records. `report.py` renders the saved JSON without
rerunning the benchmark. The `report_refresh` entry records the reporting-only
corrections made after the saved run; the timings were not rerun. `build/` is
disposable and ignored by Git.

The original portable-only measurements are preserved in `results/portable-only/`.
The current report uses a fresh run of all five paths together.
