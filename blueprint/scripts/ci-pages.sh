#!/usr/bin/env bash
# Build the blueprint site and check that the expected files exist.
# Run from the `blueprint/` directory (the GitHub workflow does this).

set -euo pipefail

lake exe vbp build

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
