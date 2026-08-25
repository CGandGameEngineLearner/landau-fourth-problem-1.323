#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_root=$(cd "$script_dir/.." && pwd)
source_file="$project_root/paper/landau_lpf_1_323.tex"
archive_path="$project_root/output/landau_lpf_1_323_arxiv_source.tar.gz"
checksum_path="$project_root/output/landau_lpf_1_323_arxiv_source.sha256"

test -f "$source_file"

# The paper has an internal thebibliography and no figure or external style
# file, so arXiv only needs this one TeX source file. The -C option stores it
# at the archive root, which makes arXiv's top-level-file detection explicit.
tar -czf "$archive_path" -C "$project_root/paper" landau_lpf_1_323.tex
sha256sum "$archive_path" | awk '{print $1 "  landau_lpf_1_323_arxiv_source.tar.gz"}' > "$checksum_path"
cat "$checksum_path"

