#!/bin/sh
set -eu
project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_root"
./scripts/lake.sh build
./scripts/lake.sh env lean Audit.lean
