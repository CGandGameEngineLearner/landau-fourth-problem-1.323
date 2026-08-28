#!/usr/bin/env bash
# Pack the committed public tree into a Zenodo/GitHub-style source zip.
# Unpublished local files (.dragonli, tmp/, .lake/, zhihu notes, generated
# archives) are excluded because they are not in Git.
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_root=$(cd "$script_dir/.." && pwd)
version="${1:-1.0.0}"
prefix="landau-fourth-problem-1.323-v${version}"
archive_path="$project_root/output/${prefix}.zip"
checksum_path="$project_root/output/${prefix}.sha256"

if [[ -n "$(git -C "$project_root" status --porcelain)" ]]; then
  echo "working tree is not clean; commit or stash before packaging" >&2
  git -C "$project_root" status --porcelain >&2
  exit 1
fi

mkdir -p "$project_root/output"
git -C "$project_root" archive \
  --format=zip \
  --prefix="${prefix}/" \
  -o "$archive_path" \
  HEAD

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$archive_path" | awk -v name="${prefix}.zip" '{print $1 "  " name}' > "$checksum_path"
else
  python3 - "$archive_path" "$checksum_path" "${prefix}.zip" <<'PY'
import hashlib, sys
src, dest, name = sys.argv[1], sys.argv[2], sys.argv[3]
digest = hashlib.sha256(open(src, "rb").read()).hexdigest()
open(dest, "w", encoding="ascii", newline="\n").write(f"{digest}  {name}\n")
PY
fi

cat "$checksum_path"
echo "$archive_path"
