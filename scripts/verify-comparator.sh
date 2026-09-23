#!/usr/bin/env bash
# Adapted from the Palomar registry template (Apache-2.0).
#
# Runs the Lean FRO comparator (https://github.com/leanprover/comparator) on this
# repository, as configured by comparator.json. It checks that every theorem
# listed there is proved in Solution.lean with exactly the statement it has in
# Challenge.lean, where every constant the statement mentions, definitions and
# their auxiliary declarations included, must be identical in the two modules;
# that the proofs use only the permitted axioms; and that both the Lean kernel
# and the independent nanoda kernel accept the solution.
#
# The comparator, lean4export, nanoda and landrun are pinned to exact commits and
# built into a cache directory, COMPARATOR_CACHE (default: .cache/comparator in
# the repository). Requirements: git, python3, cargo, elan (lake), and on Linux
# also go.
#
# Sandbox. On Linux, the comparator runs the builds, the exports and the nanoda
# replay inside the landrun (Landlock) sandbox, through scripts/landrun-wrapper.sh;
# the Lean kernel replays the exported solution in the comparator's own process.
# landrun exists only on Linux. On any other system the script stops, unless
# COMPARATOR_ALLOW_UNSANDBOXED=1 is set: then the comparator's development shim
# scripts/fake-landrun.sh stands in for landrun and runs the same commands with
# no sandbox at all. The statement comparison, the axiom check and both kernel
# replays are unchanged; only the sandbox guarantee is lost.
#
# The comparator builds Challenge and Solution itself, inside the sandbox. A
# build of Solution made outside the sandbox beforehand (an ordinary
# `lake build`, say) could have tampered with the Challenge build, so a check
# that does not trust the library starts from a .lake that holds only the
# Mathlib cache, as CI does. Fetching the Mathlib cache is fine, and done below.
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${COMPARATOR_CACHE:-"$repository_root/.cache/comparator"}

# The revisions used with Lean v4.34.0. Move them together with lean-toolchain.
comparator_commit=d03acab154d269c06e60e4de7e4cc85deebff94b
lean4export_commit=076e8e57707e813375e8f9da8bf989799ace9680
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

system=$(uname -s)
if [ "$system" = Linux ]; then
  sandbox=landrun
  if [ -n "${COMPARATOR_ALLOW_UNSANDBOXED:-}" ]; then
    echo "note: COMPARATOR_ALLOW_UNSANDBOXED is ignored on Linux; landrun is always used" >&2
  fi
elif [ "${COMPARATOR_ALLOW_UNSANDBOXED:-}" = 1 ]; then
  sandbox=none
else
  echo "error: the comparator's sandbox, landrun, needs Linux (Landlock), and this is $system" >&2
  echo "run this script on Linux, as CI does, or set COMPARATOR_ALLOW_UNSANDBOXED=1 to run" >&2
  echo "the same checks with no sandbox" >&2
  exit 1
fi

warn_unsandboxed() {
  cat >&2 <<WARNING
================================================================================
WARNING: UNSANDBOXED RUN (COMPARATOR_ALLOW_UNSANDBOXED=1 on $system)
landrun is not available here, so the comparator's development shim
fake-landrun.sh runs the builds, the exports and the nanoda replay with no sandbox.
The sandbox guarantee is lost: Solution and the library it imports are compiled
with full access to this machine. Still checked: the statements and every
definition they use against Challenge, the permitted axioms, and the replay of
the solution by the Lean kernel and by nanoda. Run on Linux for the full check.
================================================================================
WARNING
}

required_commands=(cargo git lake python3)
if [ "$sandbox" = landrun ]; then
  required_commands+=(go)
fi
for required_command in "${required_commands[@]}"; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run the comparator" >&2
    exit 1
  fi
done

# The comparator checks only what comparator.json names, so refuse settings
# under which a passing run would claim less than it seems to.
python3 - "$repository_root/comparator.json" <<'PY'
import json
import pathlib
import sys

config_path = pathlib.Path(sys.argv[1])
try:
    config = json.loads(config_path.read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    sys.exit(f"error: cannot read a valid comparator config from {config_path}: {error}")
if not isinstance(config, dict):
    sys.exit(f"error: {config_path}: the comparator config must be a JSON object")

problems = []
if config.get("enable_nanoda") is not True:
    problems.append("enable_nanoda must be exactly true; the nanoda replay is part of the check")
theorem_names = config.get("theorem_names")
if not (isinstance(theorem_names, list) and theorem_names
        and all(isinstance(name, str) and name for name in theorem_names)):
    problems.append("theorem_names must be a non-empty list of declaration names")
if config.get("definition_names", []) != []:
    problems.append("definition_names must be empty: a definition hole is compared by its type "
                    "only, and the definitions of this repository must be compared in full")
permitted_axioms = config.get("permitted_axioms")
if not (isinstance(permitted_axioms, list)
        and set(permitted_axioms) <= {"propext", "Quot.sound", "Classical.choice"}):
    problems.append("permitted_axioms may list only propext, Quot.sound and Classical.choice")
for problem in problems:
    print(f"error: {config_path}: {problem}", file=sys.stderr)
if problems:
    sys.exit(1)
PY

if [ "$sandbox" = none ]; then
  warn_unsandboxed
fi

mkdir -p "$cache_root"
cache_root=$(cd "$cache_root" && pwd)
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"
mkdir -p "$bin_dir"

checkout_exact() {
  local repository=$1 destination=$2 commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --quiet --filter=blob:none "$repository" "$destination"
  fi
  if ! git -C "$destination" cat-file -e "$commit^{commit}" 2>/dev/null; then
    git -C "$destination" fetch --quiet --depth 1 origin "$commit"
  fi
  git -C "$destination" checkout --quiet --force --detach "$commit"
  if [ "$(git -C "$destination" rev-parse HEAD)" != "$commit" ]; then
    echo "error: $destination is not at the pinned commit $commit" >&2
    exit 1
  fi
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"
checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

# lean4export reads the project's .olean files, so it must be built with the
# project's toolchain; the comparator parses its output with the same library.
project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
for tool_dir in "$lean4export_dir" "$comparator_dir"; do
  tool=$(basename "$tool_dir")
  if [ ! -f "$tool_dir/lean-toolchain" ]; then
    echo "error: the pinned $tool revision has no lean-toolchain file" >&2
    exit 1
  fi
  tool_toolchain=$(tr -d '[:space:]' < "$tool_dir/lean-toolchain")
  if [ "$tool_toolchain" != "$project_toolchain" ]; then
    echo "error: the pinned $tool revision targets $tool_toolchain, but lean-toolchain is $project_toolchain" >&2
    echo "move the pins in scripts/verify-comparator.sh together with lean-toolchain" >&2
    exit 1
  fi
done
comparator_export_rev=$(python3 - "$comparator_dir/lake-manifest.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as manifest:
    packages = json.load(manifest)["packages"]
print(next((package["rev"] for package in packages if package["name"] == "lean4export"), ""))
PY
)
if [ "$comparator_export_rev" != "$lean4export_commit" ]; then
  echo "error: the pinned comparator parses exports with lean4export ${comparator_export_rev:-(none)}," >&2
  echo "but the exporter is pinned to $lean4export_commit" >&2
  exit 1
fi

if [ "$sandbox" = landrun ]; then
  GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"
  landrun_binary="$bin_dir/landrun"
else
  landrun_binary="$comparator_dir/scripts/fake-landrun.sh"
fi

(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
lake exe cache get

if [ "$sandbox" = none ]; then
  trap 'echo "reminder: this comparator run was NOT sandboxed (COMPARATOR_ALLOW_UNSANDBOXED=1)" >&2' EXIT
fi
LANDRUN_BIN="$landrun_binary" \
COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
  lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json
