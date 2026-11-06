#!/usr/bin/env bash
set -euo pipefail

# Use the kernels bundled with Lean, as in Palomar's official starter:
# https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406
cd "$(dirname "$0")/.."
if [[ "$(uname -s)" != Linux ]]; then
  echo "Comparator's sandbox requires Linux. Run this check in GitHub Actions." >&2
  exit 1
fi
command -v bwrap >/dev/null || { echo "Install bubblewrap first." >&2; exit 1; }
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  [[ -x "$prefix/bin/$tool" ]] || { echo "Missing toolchain binary: $tool" >&2; exit 1; }
done

# The submitted config cannot set external_kernels; Palomar adds them itself.
config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - "$prefix" "$config" <<'PY'
import json
import pathlib
import sys

prefix, output = sys.argv[1:]
config = json.loads(pathlib.Path("comparator.json").read_text())
if "external_kernels" in config:
    raise SystemExit("external_kernels is not permitted in the submitted config")
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(output).write_text(json.dumps(config))
PY

lake exe cache get
lake comparator --config "$config"
