#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

die() { printf '%s\n' "$*" >&2; exit 1; }
count_rows() { awk 'END { print NR - 1 }' "$1"; }
count_token() { local n; n=$(rg -c ",\"$2\"," "$1" || true); printf '%s' "${n:-0}"; }

[[ $(count_rows STATEMENT_LEDGER.csv) -eq 15 ]] || die 'statement row count mismatch'
[[ $(count_rows EQUATION_LEDGER.csv) -eq 82 ]] || die 'equation row count mismatch'
[[ $(count_rows UNNUMBERED_LEDGER.csv) -eq 62 ]] || die 'unnumbered row count mismatch'

[[ $(count_token STATEMENT_LEDGER.csv PROVED) -eq 15 ]] || die 'statement status mismatch'
[[ $(count_token EQUATION_LEDGER.csv PROVED) -eq 73 ]] || die 'equation proved count mismatch'
[[ $(count_token EQUATION_LEDGER.csv DEFINITION) -eq 9 ]] || die 'equation definition count mismatch'
[[ $(count_token UNNUMBERED_LEDGER.csv proved) -eq 62 ]] || die 'unnumbered status mismatch'
[[ $(count_token UNNUMBERED_LEDGER.csv COMPLETE) -eq 62 ]] || die 'unnumbered progress mismatch'

test "$(sed -nE 's/.*\\label\{(eq:[^}]+)\}.*/\1/p' DR_Yaglom.tex | sort -u)" = \
  "$(sed -nE '2,$s/^"([^\"]*)".*/\1/p' EQUATION_LEDGER.csv | sort -u)" ||
  die 'equation labels differ from TeX labels'

check_paths() {
  local file=$1 field_re=$2
  sed -nE "2,\$s/${field_re}/\\1/p" "$file" | tr ';' '\n' |
    sed 's/^[[:space:]]*//;s/[[:space:]]*$//' | sed '/^$/d' |
    while IFS= read -r path; do
      [[ -f "$path" ]] || die "missing ledger path: $path"
    done
}

check_paths STATEMENT_LEDGER.csv '^"[^"]*","[^"]*","[^"]*","[^"]*","([^"]*)".*$'
check_paths EQUATION_LEDGER.csv '^"[^"]*","[^"]*","([^"]*)".*$'
check_paths UNNUMBERED_LEDGER.csv '^"[^"]*","[^"]*","([^"]*)".*$'

expected_decls=$(mktemp)
audited_decls=$(mktemp)
trap 'rm -f "$expected_decls" "$audited_decls"' EXIT
{
  sed -nE '2,$s/^"[^"]*","[^"]*","[^"]*","[^"]*","[^"]*","([^"]*)".*/\1/p' STATEMENT_LEDGER.csv
  sed -nE '2,$s/^"[^"]*","[^"]*","[^"]*","([^"]*)".*/\1/p' EQUATION_LEDGER.csv
  sed -nE '2,$s/^"[^"]*","[^"]*","[^"]*","([^"]*)".*/\1/p' UNNUMBERED_LEDGER.csv
} | tr ';' '\n' | sed 's/^[[:space:]]*//;s/[[:space:]]*$//' |
  sed '/^$/d' | sort -u > "$expected_decls"
sed -nE 's/^#check ([^ ]+)$/\1/p' DerridaRetaux/Audit/AllSourceDecls.lean |
  sort -u > "$audited_decls"
cmp -s "$expected_decls" "$audited_decls" || die 'AllSourceDecls coverage mismatch'

if rg -n 'H[0-9]+[a-z]?' STATEMENT_LEDGER.csv EQUATION_LEDGER.csv UNNUMBERED_LEDGER.csv |
    rg -v 'H1a|H1b|H2|H3'; then
  die 'unapproved human-input tag in ledger'
fi

printf '%s\n' \
  'LEDGERS_OK statements=15 equations=82 unnumbered=62' \
  'statement_statuses=15_proved+0_partial+0_unformalized' \
  'equation_statuses=73_proved+9_definition+0_partial+0_open' \
  'unnumbered_statuses=62_proved+0_blocked' \
  'unnumbered_progress=62_complete+0_partial+0_open' \
  'labels=true paths=true all_source_decls=true inputs=true'
