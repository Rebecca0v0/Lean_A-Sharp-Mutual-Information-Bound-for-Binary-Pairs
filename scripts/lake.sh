#!/bin/sh
# Use the optional project-local installation, or an existing system Lake.
set -eu
project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_root"
if [ -x "$project_root/.tooling/elan/bin/lake" ]; then
  export ELAN_HOME="$project_root/.tooling/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
export MATHLIB_CACHE_DIR="$project_root/.tooling/mathlib-cache"
exec lake "$@"
