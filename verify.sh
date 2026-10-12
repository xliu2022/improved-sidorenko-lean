#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
python3 scripts/check-lean-sources.py
python3 verification/check_sources.py
ruby scripts/validate-formalization.rb
lake build
lake env lean verification/Audit.lean
if [[ "${1:-}" == "--comparator" ]]; then
  ./scripts/verify-comparator.sh
fi
