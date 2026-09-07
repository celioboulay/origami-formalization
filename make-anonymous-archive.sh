#!/usr/bin/env bash
set -euo pipefail

# Create a source-only archive suitable for anonymous review.
root_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
archive_path=${1:-"$(dirname "$root_dir")/origami-anonymous.zip"}
stage_dir=$(mktemp -d)
archive_root=origami-anonymous

cleanup() {
  rm -rf -- "$stage_dir"
}
trap cleanup EXIT

mkdir -p "$stage_dir/$archive_root"
tar -C "$root_dir" \
  --exclude='.git' \
  --exclude='.git/*' \
  --exclude='.lake' \
  --exclude='.lake/*' \
  --exclude='.idea' \
  --exclude='.idea/*' \
  --exclude='.venv' \
  --exclude='.venv/*' \
  --exclude='.agents' \
  --exclude='.agents/*' \
  --exclude='.claude' \
  --exclude='.claude/*' \
  --exclude='.codex' \
  --exclude='.codex/*' \
  --exclude='__pycache__' \
  --exclude='__pycache__/*' \
  --exclude='data' \
  --exclude='data/*' \
  --exclude='Origami/generated' \
  --exclude='Origami/generated/*' \
  --exclude='Origami/outdated_affine_huzita' \
  --exclude='Origami/outdated_affine_huzita/*' \
  --exclude='assets creation.odp' \
  --exclude='project description.txt' \
  --exclude='crane_huzita_instructions.md' \
  --exclude='related_work_draft.md' \
  --exclude='related_work_fact_check.md' \
  --exclude='*.DS_Store' \
  --exclude='*.olean' \
  --exclude='*.ilean' \
  --exclude='*/build' \
  --exclude='*/build/*' \
  --exclude='*/target' \
  --exclude='*/target/*' \
  --exclude='*/node_modules' \
  --exclude='*/node_modules/*' \
  -cf - . | tar -C "$stage_dir/$archive_root" -xf -

if [ -e "$archive_path" ]; then
  printf 'Refusing to overwrite existing archive: %s\n' "$archive_path" >&2
  exit 1
fi
(cd "$stage_dir" && zip -qr "$archive_path" "$archive_root")
printf 'Created %s\n' "$archive_path"
