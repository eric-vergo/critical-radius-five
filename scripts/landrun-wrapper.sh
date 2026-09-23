#!/usr/bin/env bash
# Adapted from the Palomar registry template (Apache-2.0).
#
# Stands between the comparator and landrun: the comparator is pointed at this
# script (COMPARATOR_LANDRUN), and the script executes the landrun binary named
# by LANDRUN_BIN after checking the options it was given.
#
# landrun's current CLI needs an explicit `--` between its own options and the
# sandboxed command; without it, landrun would consume lean4export's own `--`
# separator. The wrapper therefore always emits exactly one `--`, whether or not
# the comparator supplied one.
set -euo pipefail

landrun_binary=${LANDRUN_BIN:?LANDRUN_BIN must name the pinned landrun binary}
landrun_options=()

# landrun's --unrestricted-* options each switch off a whole class of Landlock
# restriction. The pinned comparator never asks for one, and passing them
# through would let a later comparator disable the sandbox without anyone
# noticing, so they are refused by name. landrun accepts one or two leading
# dashes for every option, so both spellings are refused.
while [ "$#" -gt 0 ]; do
  case "$1" in
    -unrestricted-*|--unrestricted-*)
      echo "error: landrun option $1 switches off part of the sandbox" >&2
      echo "the comparator must not request it; refusing to run $landrun_binary" >&2
      exit 2
      ;;
    --best-effort|-ldd|--ldd|-add-exec|--add-exec|--ignore-missing|--log-disable-originating|--log-enable-subprocesses|--log-disable-subdomains)
      landrun_options+=("$1")
      shift
      ;;
    --log-level|--ro|--rox|--rw|--rwx|--unix|--bind-tcp|--connect-tcp|--env)
      if [ "$#" -lt 2 ]; then
        echo "error: landrun option $1 is missing its value" >&2
        exit 2
      fi
      landrun_options+=("$1" "$2")
      shift 2
      ;;
    --)
      # The comparator's own end-of-options delimiter. Everything after it is
      # the sandboxed command; the exec below re-adds a single `--`.
      shift
      break
      ;;
    -*)
      echo "error: unrecognized landrun option $1; review scripts/landrun-wrapper.sh" >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [ "$#" -eq 0 ]; then
  echo "error: the comparator supplied no sandboxed command" >&2
  exit 2
fi

# The `+` expansion keeps an empty option list legal under `set -u` in bash 3.2.
exec "$landrun_binary" ${landrun_options[@]+"${landrun_options[@]}"} -- "$@"
