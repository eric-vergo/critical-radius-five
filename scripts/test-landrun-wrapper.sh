#!/usr/bin/env bash
# Adapted from the Palomar registry template (Apache-2.0).
#
# Exercises scripts/landrun-wrapper.sh against a stub landrun that records the
# argument vector it receives. The properties checked here are the sandbox's
# contract: the options the comparator actually sends reach landrun unchanged,
# followed by exactly one `--`, and any option that would switch off a Landlock
# restriction stops the run instead.
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
wrapper="$repository_root/scripts/landrun-wrapper.sh"
work_dir=$(mktemp -d)
trap 'rm -rf "$work_dir"' EXIT

stub="$work_dir/landrun-stub.sh"
cat >"$stub" <<'STUB'
#!/usr/bin/env bash
printf '%s\n' "$@" >"$LANDRUN_TEST_ARGV"
STUB
chmod +x "$stub"

failures=0
export LANDRUN_BIN="$stub"
export LANDRUN_TEST_ARGV="$work_dir/argv"

report_failure() {
  echo "FAIL: $1" >&2
  failures=$((failures + 1))
}

# Runs the wrapper, capturing its status, its stderr and the stub's argument vector.
run_wrapper() {
  : >"$LANDRUN_TEST_ARGV"
  set +e
  wrapper_stderr=$("$wrapper" "$@" 2>&1 >/dev/null)
  wrapper_status=$?
  set -e
  wrapper_argv=$(cat "$LANDRUN_TEST_ARGV")
}

assert_passthrough() {
  local description=$1 expected=$2
  shift 2
  run_wrapper "$@"
  if [ "$wrapper_status" -ne 0 ]; then
    report_failure "$description: wrapper exited $wrapper_status: $wrapper_stderr"
  elif [ "$wrapper_argv" != "$expected" ]; then
    report_failure "$description: landrun received
$wrapper_argv
but expected
$expected"
  fi
}

assert_refused() {
  local description=$1 flag=$2
  shift 2
  run_wrapper "$@"
  if [ "$wrapper_status" -ne 2 ]; then
    report_failure "$description: wrapper exited $wrapper_status, expected 2"
  elif [ -s "$LANDRUN_TEST_ARGV" ]; then
    report_failure "$description: landrun ran anyway with
$wrapper_argv"
  elif [ "${wrapper_stderr#*"$flag"}" = "$wrapper_stderr" ]; then
    report_failure "$description: the refusal does not name $flag: $wrapper_stderr"
  fi
}

# The option vector the pinned comparator builds (buildLandrunArgs), which
# already ends its options with `--`.
assert_passthrough "the comparator's own options reach landrun" \
  '--best-effort
--ro
/
--rw
/dev
-ldd
-add-exec
--env
PATH
--ro
/workspace
--rwx
/workspace/.lake
--rox
/toolchain
--
lake
build
Solution' \
  --best-effort --ro / --rw /dev -ldd -add-exec --env PATH \
  --ro /workspace --rwx /workspace/.lake --rox /toolchain \
  -- lake build Solution

# Without a `--` from the comparator, the wrapper adds exactly one.
assert_passthrough "a missing -- is added once" \
  '--best-effort
--
true' \
  --best-effort true

# -add-exec narrows the executable set rather than lifting a restriction, and
# the comparator sends it on every run, so both spellings stay allowed.
assert_passthrough "-add-exec stays allowed" \
  '-add-exec
--
true' \
  -add-exec true
assert_passthrough "--add-exec stays allowed" \
  '--add-exec
--
true' \
  --add-exec true

for flag in --unrestricted-filesystem --unrestricted-network --unrestricted-scoped \
  -unrestricted-filesystem -unrestricted-network -unrestricted-scoped \
  --unrestricted-filesystem=true; do
  assert_refused "$flag is refused" "$flag" --best-effort "$flag" --ro / true
done
assert_refused "--unrestricted-filesystem before -- is refused" \
  "--unrestricted-filesystem" --best-effort --unrestricted-filesystem -- true

# After the delimiter, or after the command, it is an argument of the command.
assert_passthrough "--unrestricted-filesystem after -- is a command argument" \
  '--best-effort
--
solver
--unrestricted-filesystem' \
  --best-effort -- solver --unrestricted-filesystem
assert_passthrough "the sandboxed command keeps its own arguments" \
  '--best-effort
--
solver
--unrestricted-filesystem' \
  --best-effort solver --unrestricted-filesystem

assert_refused "an unknown option is refused" "--brand-new-flag" --brand-new-flag true
assert_refused "an option missing its value is refused" "--ro" --ro

run_wrapper --best-effort --
if [ "$wrapper_status" -ne 2 ]; then
  report_failure "a bare -- with no command is refused: wrapper exited $wrapper_status, expected 2"
fi
run_wrapper --best-effort
if [ "$wrapper_status" -ne 2 ]; then
  report_failure "a missing command is refused: wrapper exited $wrapper_status, expected 2"
fi

if [ "$failures" -ne 0 ]; then
  echo "$failures landrun-wrapper.sh check(s) failed" >&2
  exit 1
fi

echo "landrun-wrapper.sh checks passed"
