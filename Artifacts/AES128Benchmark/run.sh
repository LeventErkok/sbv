#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# The benchmark starts only when the machine is quiet: 1-minute load average below a
# quarter of the logical CPUs by default (the timed code is single-threaded). Override
# with MAX_LOAD or ALLOW_BUSY=1; the threshold and starting load are recorded either way.
MAX_LOAD=${MAX_LOAD:-$(python3 -c 'import os; print(os.cpu_count() / 4)')}
WAIT_SECONDS=${WAIT_SECONDS:-900}
mkdir -p results
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  > results/configure.log 2>&1
cmake --build build -j 4 > results/build.log 2>&1
python3 provenance.py
python3 codesize.py | tee results/codesize.txt
build/aes128_benchmark --validate-only | tee results/validation.txt
waited=0
while ! python3 -c "import os,sys; sys.exit(0 if os.getloadavg()[0] < float('$MAX_LOAD') else 1)"; do
  if [ "$waited" -ge "$WAIT_SECONDS" ]; then
    if [ "${ALLOW_BUSY:-0}" = 1 ]; then echo "WARNING: starting under load" >&2; break; fi
    echo "1-minute load average stayed above $MAX_LOAD for ${WAIT_SECONDS}s; not benchmarking." >&2
    echo "Quiet the machine or set ALLOW_BUSY=1 (the load will still be recorded)." >&2
    exit 1
  fi
  echo "Waiting for load average below $MAX_LOAD (now $(python3 -c 'import os; print(round(os.getloadavg()[0],2))'))..."
  sleep 15; waited=$((waited + 15))
done
python3 - "$MAX_LOAD" "$waited" <<'PY'
import json, os, sys
config = {"max_load_threshold": float(sys.argv[1]), "load_average_at_start": os.getloadavg(),
          "logical_cpus": os.cpu_count(), "seconds_waited": int(sys.argv[2])}
open("results/run_config.json", "w").write(json.dumps(config, indent=2) + "\n")
PY
build/aes128_benchmark \
  --benchmark_min_time=0.5s \
  --benchmark_min_warmup_time=0.2 \
  --benchmark_repetitions=9 \
  --benchmark_enable_random_interleaving=true \
  --benchmark_out=results/benchmark.json --benchmark_out_format=json \
  2>&1 | tee results/benchmark.txt
python3 scrub.py
python3 report.py
