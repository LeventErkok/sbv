#!/usr/bin/env python3
"""Render saved Google Benchmark repetitions as a self-contained HTML report."""
import csv
import html
import json
import re
from pathlib import Path
import statistics

root = Path(__file__).resolve().parent
data = json.loads((root / "results/benchmark.json").read_text())
metadata = json.loads((root / "results/provenance.json").read_text())
run_config = json.loads((root / "results/run_config.json").read_text())
groups = {}
for row in data["benchmarks"]:
    if row.get("run_type") == "iteration":
        impl, size = row["run_name"].split("/")[:2]
        size = int(size)
        # Default timing is thread CPU time; retain wall time in the raw JSON.
        factor = {"ns": 1, "us": 1000, "ms": 1e6, "s": 1e9}[row["time_unit"]]
        groups.setdefault((impl, size), []).append(row["cpu_time"] * factor / (size / 16))

summary = []
for size in (16, 1024, 16384):
    baseline = statistics.median(groups[("SBV", size)])
    for impl in ("SBV", "SBV_native_words", "BearSSL_big", "tiny_AES_c", "OpenSSL_EVP_block", "OpenSSL_EVP_bulk"):
        values = groups[(impl, size)]
        median = statistics.median(values)
        summary.append(dict(implementation=impl, buffer_bytes=size,
            median_ns_per_block=median, min_ns_per_block=min(values),
            max_ns_per_block=max(values),
            cv_percent=100 * statistics.stdev(values) / statistics.mean(values),
            mib_per_second=16e9 / median / 2**20, speed_relative_to_sbv=baseline/median,
            repetitions=len(values)))
with (root / "results/summary.csv").open("w", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=summary[0].keys())
    writer.writeheader()
    writer.writerows(summary)

escape = html.escape
tables = []
for size in (16, 1024, 16384):
    rows = [r for r in summary if r["buffer_bytes"] == size]
    maximum = max(r["mib_per_second"] for r in rows)
    body = "".join(
        f'<tr><th>{escape(r["implementation"])}</th>'
        f'<td>{r["median_ns_per_block"]:.2f}</td>'
        f'<td>{r["mib_per_second"]:.1f}</td>'
        f'<td>{r["speed_relative_to_sbv"]:.2f}×</td>'
        f'<td>{r["min_ns_per_block"]:.2f}–{r["max_ns_per_block"]:.2f}</td>'
        f'<td>{r["cv_percent"]:.1f}%</td></tr>' for r in rows)
    bars = "".join(
        f'<div class="barrow"><span>{escape(r["implementation"])}</span>'
        f'<div class="track"><div class="bar" style="width:{r["mib_per_second"]/maximum*100:.2f}%"></div></div>'
        f'<span class="barvalue">{r["mib_per_second"]:.1f} MiB/s</span></div>' for r in rows)
    tables.append(f'<section><h2>{size:,}-byte buffer · {size//16:,} blocks per iteration</h2>'
        f'{bars}<div class="scroll"><table><thead><tr><th>Implementation</th><th>ns/block ↓</th>'
        '<th>MiB/s ↑</th><th>Speed / SBV ↑</th><th>Min–max ns/block</th><th>CV</th>'
        f'</tr></thead><tbody>{body}</tbody></table></div></section>')

bulk = {r["implementation"]: r for r in summary if r["buffer_bytes"] == 16384}
small = {r["implementation"]: r for r in summary if r["buffer_bytes"] == 16}
sbv = bulk["SBV"]
def faster(a, b):
    """How much faster implementation a is than b, as a plain sentence fragment."""
    return bulk[b]["median_ns_per_block"] / bulk[a]["median_ns_per_block"]
bear, tiny = faster("SBV", "BearSSL_big"), faster("SBV", "tiny_AES_c")
words = faster("SBV_native_words", "SBV")
hw_block = faster("OpenSSL_EVP_block", "SBV")
hw_bulk = faster("OpenSSL_EVP_bulk", "SBV")
headline = (f'Among portable C implementations on this machine, SBV-generated AES-128 encryption '
            f'ran at {sbv["mib_per_second"]:.0f} MiB/s ({sbv["median_ns_per_block"]:.1f} ns/block) '
            f'with 16 KiB buffers: {bear:.2f}× the throughput of BearSSL and {tiny:.2f}× that of tiny-AES-c.')
sizes = json.loads((root / "results/codesize.json").read_text())
size_rows = "".join(
    f'<tr><th>{escape(r["implementation"])}</th><td>{r["code_bytes"]:,}</td>'
    f'<td>{r["constant_bytes"]:,}</td><td>{r["total_bytes"]:,}</td>'
    f'<td>{r["source_lines"]:,}</td><td class="left">{escape(r["scope"])}</td></tr>' for r in sizes)
by_name = {r["implementation"]: r for r in sizes}
size_ratio = by_name["SBV encryption"]["total_bytes"] / by_name["BearSSL aes_big"]["total_bytes"]
versions = "".join(f'<li><a href="{escape(v["url"])}">{escape(k)}</a>: '
                   f'<code>{escape(v["commit"])}</code></li>'
                   for k, v in metadata["sources"].items())
warnings = data.get("context", {}).get("library_build_type", "unknown")
cpu_info = data["context"]["openssl_cpu_info"]
armcap = re.search(r"OPENSSL_armcap=0x([0-9a-fA-F]+)", cpu_info)
hardware_summary = "OpenSSL uses runtime dispatch; hardware AES use is not established by this report."
acceleration_note = "The recorded capabilities are not decoded for this platform; no hardware AES claim is made."
if armcap:
    enabled = bool(int(armcap.group(1), 16) & 4)
    hardware_summary = ("OpenSSL's recorded ARM capabilities " + ("enable" if enabled else "disable")
                        + " hardware AES dispatch.")
    acceleration_note = ("The recorded ARM capability mask " + ("includes" if enabled else "excludes")
        + ' the hardware AES bit (1 &lt;&lt; 2), defined in '
        + '<a href="https://github.com/openssl/openssl/blob/openssl-3.6.3/crypto/arm_arch.h">OpenSSL arm_arch.h</a>. '
        + 'This identifies dispatch eligibility, not an instruction trace.')
hardware = (hardware_summary + f' Its throughput was {hw_block:.1f}× SBV with one call per block '
            f'and {hw_bulk:.1f}× SBV with one call per buffer.')
console_path = root / "results/benchmark.txt"
console = console_path.read_text() if console_path.exists() else ""
clock_note = ""
if ("Unable to determine clock rate" in console
        or "Estimated CPU frequency may be incorrect" in console):
    clock_note = ('<p>The saved benchmark console output warns that the CPU frequency metadata '
                  'may be unreliable. The reported ns/block and MiB/s use CPU timers, '
                  'not that frequency estimate.</p>')
compiler = metadata["compiler"].splitlines()[0]
document = f'''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>AES128 reused-key benchmark</title>
<style>
:root{{font-family:system-ui,sans-serif;color:#192b3c;background:#f3f6f9}}
body{{max-width:1080px;margin:40px auto;padding:0 24px;line-height:1.6}}
h1{{font-size:2.4rem;line-height:1.15}}h2{{font-size:1.25rem}}
section,.lead{{background:white;padding:24px;border-radius:12px;margin:24px 0}}
.lead{{border-left:5px solid #157c80}}table{{border-collapse:collapse;width:100%;font-size:.9rem}}
td,th{{padding:10px;text-align:right;border-bottom:1px solid #ddd;white-space:nowrap}}
th:first-child,td.left{{text-align:left}}.scroll{{overflow:auto}}code{{overflow-wrap:anywhere}}
.barrow{{display:flex;align-items:center;gap:12px;margin:8px 0;font-size:.85rem}}
.barrow span{{width:180px;flex-shrink:0}}.track{{flex:1;background:#edf2f6}}.bar{{background:#157c80;height:24px}}
.barrow .barvalue{{width:110px}}
a{{color:#126d9a}}pre{{overflow:auto;background:#edf2f6;padding:16px}}
</style><main>
<p>SBV → C · AES-128 · encryption only</p><h1>Reused-key encryption performance</h1>
<div class="lead"><strong>{escape(headline)}</strong>
<p>{escape(hardware)}</p>
<p>Measured once, on {escape(metadata["machine"])} using {escape(compiler)}. Results on other CPUs or compilers
may differ. Expanded keys are reused throughout each timed run.</p></div>
{''.join(tables)}
<section><h2>Code size: what the speed costs</h2>
<p>Sizes below are compiled machine code and read-only data (tables) for the object files the benchmark links,
built with the same flags as the timed code.</p>
<div class="scroll"><table><thead><tr><th>Object</th><th>Code (bytes)</th><th>Tables (bytes)</th>
<th>Total (bytes)</th><th>Source lines</th><th>Covers</th></tr></thead><tbody>{size_rows}</tbody></table></div>
<p>SBV's block-encryption function is {size_ratio:.1f}× the size of BearSSL's, and its key schedule is far larger
still (generated straight-line code, not timed here). The generated encryptor has no round loop and carries
four separate 1 KiB lookup tables plus a 256-byte S-box. Each ordinary round computes four words,
each using four table lookups combined with XORs; the final round uses the S-box. BearSSL's <code>aes_big</code> keeps one
table, derives the other three by rotating its entries, and loops over rounds. tiny-AES-c computes each byte
with an S-box and <code>xtime</code> arithmetic. That is consistent with SBV trading space (code and cache footprint)
for fewer instructions per block, but this benchmark did not vary table size or unrolling independently, so it
shows a correlation in these three implementations, not an isolated cause. tiny-AES-c's object also contains decryption and
key expansion, which were not separated in this measurement, so its total overstates an encrypt-only build.</p></section>
<section><h2>What was measured</h2>
<p>Each iteration encrypts an immutable buffer of independent 16-byte blocks into a separate output buffer.
The same expanded key is reused. Key expansion, allocation, input generation, and validation occur before timing.
No output block feeds the next input. All implementations receive identical input bytes.</p>
<p>SBV uses its generated block-encryption function with a 44-word expanded encryption key.
For <code>SBV</code> the timed adapter loads and stores big-endian words; <code>SBV_native_words</code> calls the same
function on pre-converted 32-bit words, which isolates the generated code from that adapter. BearSSL uses its internal single-block
<code>br_aes_big_encrypt</code> primitive directly; tiny-AES-c uses <code>AES_ECB_encrypt</code>.
Their in-place APIs receive a 16-byte copy from the input. All paths include the work needed for
the same byte-buffer interface. There is no padding or chaining between blocks.</p>
<p>OpenSSL uses AES-128-ECB through the default provider and
<a href="https://docs.openssl.org/3.5/man3/EVP_EncryptInit/">EVP_EncryptUpdate</a>, with padding disabled.
The cipher, context, key setup, and a first encryption call are completed before timing.
<code>OpenSSL_EVP_block</code> calls EVP once per block; <code>OpenSSL_EVP_bulk</code> calls it once
per entire buffer, allowing internal parallel processing and amortizing EVP overhead.
Both include EVP return-value and output-length checks. The harness uses OpenSSL's runtime dispatch.</p>
<p>Library: {escape(data["context"]["openssl_version"])}; provider:
{escape(data["context"]["openssl_provider"])}; detected capabilities:
<code>{escape(data["context"]["openssl_cpu_info"])}</code>.
OpenSSL is a prebuilt installed library; it does not share the portable C compiler flags.
Its own build flags are recorded in the raw JSON.</p>
<p>{acceleration_note}</p>
<p>Google Benchmark uses 0.2 seconds of warmup, a minimum 0.5 seconds per measurement,
and nine randomly interleaved repetitions per case. Tables show the median thread CPU time
normalized per block. Throughput is calculated from that median; CV is the sample standard
deviation divided by the mean. Raw JSON also contains wall times. Compiler barriers make output
writes observable once per batch. The three portable C implementations use {escape(compiler)}.
Recorded build flags: <code>{escape(metadata["build_flags"])}</code>. Google Benchmark build: {escape(warnings)}.</p>
</section><section><h2>Validation and interpretation</h2>
<p>Before timing, all four implementations pass the FIPS-197 Appendix C.1 AES128 known-answer vector
and agree on 1,024 deterministic pseudorandom key/plaintext pairs. A separate validation run is saved
in <a href="results/validation.txt">validation.txt</a>. OpenSSL bulk calls and continued context reuse are also checked at all buffer sizes.</p>
<p>These are warm-buffer, single-thread measurements, including function-call and adapter overhead.
Larger buffers amortize benchmark-loop overhead; the portable implementations and OpenSSL block path still make one encryption call per block. OpenSSL bulk makes one call per buffer.
The process was not pinned to a CPU, and system load, scheduling, and frequency changes can affect results.
Starting load averages reported by Google Benchmark: {escape(str(data["context"].get("load_avg", "unavailable")))}.
Min–max and CV describe nine repetitions, not confidence intervals.</p>
{clock_note}
<p>The benchmark waits until the 1-minute load average is below {run_config["max_load_threshold"]:g}
on a host with {run_config["logical_cpus"]} logical CPUs before timing; it waited
{run_config["seconds_waited"]} s and started at load {run_config["load_average_at_start"][0]:.2f}.
The threshold is configurable, and passing it does not establish that the machine was idle.
Background activity, thermal management, and scheduling can affect results.
Small differences between implementations should not be generalized without repeating them elsewhere.</p>
<p>This comparison does not measure cold caches, key expansion, decryption, or authenticated encryption.
The three portable implementations use data-dependent table lookups; the comparison makes no constant-time security claim.
OpenSSL uses runtime dispatch and may select architecture-specific implementations; interpret its timings alongside the recorded capabilities above.</p></section>
<section><h2>Reproduce and inspect</h2>
<pre>cd Artifacts/AES128Benchmark
bash run.sh</pre>
<p>Requires CMake, a C/C++ compiler, Python 3, and installed OpenSSL 3 development headers/libraries.
The three portable implementations and Google Benchmark are vendored; OpenSSL is an external dependency.
rebuilding this benchmark does not require Haskell or a network connection.
See <a href="README.md">README.md</a> for regenerating the SBV C.</p>
<ul><li><a href="results/benchmark.json">Raw measurements (JSON)</a> ·
<a href="results/benchmark.txt">Console output</a> · <a href="results/summary.csv">Summary CSV</a></li>
<li><a href="benchmark.cpp">Benchmark harness</a> · <a href="CMakeLists.txt">Build configuration</a> ·
<a href="generated/aes128BlockEncrypt.c">Generated SBV encryptor</a></li>
<li><a href="results/portable-only/benchmark.json">Original portable-only run</a></li>
<li><a href="results/provenance.json">Machine, toolchain, source revisions and SHA-256 hashes</a></li></ul>
<p>Run recorded at {escape(data["context"].get("date", "unknown"))}.
SBV checkout: <code>{escape(metadata["sbv_commit"])}</code>
({"with tracked modifications: " + escape(", ".join(metadata["sbv_dirty_paths"])) if metadata.get("sbv_tree_dirty") else "clean tracked tree"}).
Compiler: {escape(metadata["compiler"].splitlines()[0])}.</p><ul>{versions}</ul>
</section></main></html>'''
(root / "report.html").write_text(document)
print(headline)
print(f"Wrote {root / 'report.html'}")
