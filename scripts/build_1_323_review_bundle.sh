#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_root=$(cd "$script_dir/.." && pwd)
archive_path="$project_root/output/landau-1.323-review-bundle.tar.gz"
checksum_path="$project_root/output/landau-1.323-review-bundle.sha256"

bundle_files=(
  README.md
  LICENSE
  LICENSE-PAPER.md
  CITATION.cff
  .zenodo.json
  ARXIV_SUBMISSION_GUIDE.md
  .gitignore
  lean
  paper
  notes/HARMAN_RECURSIVE_1_323_ANALYTIC_TRANSFER_AUDIT_2026-08-25.md
  notes/PUBLICATION_READINESS_1_323_2026-08-25.md
  notes/SOURCE_LOCK_1_323_2026-08-25.md
  scripts/audit_harman_recursive_branch_coverage.py
  scripts/audit_harman_recursive_tail.py
  scripts/certify_harman_recursive_tail.cpp
  scripts/build_1_323_review_bundle.sh
  scripts/package_arxiv_source.sh
  output/landau_lpf_1_323.pdf
)

for bundle_file in "${bundle_files[@]}"; do
  if [[ ! -e "$project_root/$bundle_file" ]]; then
    echo "missing review-bundle input: $bundle_file" >&2
    exit 1
  fi
done

tar --exclude='lean/.lake' --exclude='lean/build' \
  -czf "$archive_path" -C "$project_root" "${bundle_files[@]}"
sha256sum "$archive_path" | awk '{print $1 "  landau-1.323-review-bundle.tar.gz"}' > "$checksum_path"
cat "$checksum_path"
