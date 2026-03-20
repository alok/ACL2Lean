#!/usr/bin/env bash
# Translate ACL2 .lisp files to Lean and optionally verify they compile.
#
# Usage:
#   ./scripts/translate-book.sh acl2_samples/sorting/orderedp.lisp   # single file
#   ./scripts/translate-book.sh acl2_samples/sorting/                # whole directory
#   ./scripts/translate-book.sh acl2_samples/sorting/ --verify       # translate + check
#
# Output goes to ACL2Lean/Translated/<BookName>.lean
# Files are named by converting the ACL2 book name to PascalCase:
#   orderedp.lisp         -> Orderedp.lean
#   how-many.lisp         -> HowMany.lean
#   ordered-perms.lisp    -> OrderedPerms.lean

set -euo pipefail

OUTDIR="ACL2Lean/Translated"
VERIFY=false

# Parse args
TARGETS=()
for arg in "$@"; do
    if [ "$arg" = "--verify" ] || [ "$arg" = "-v" ]; then
        VERIFY=true
    else
        TARGETS+=("$arg")
    fi
done

if [ ${#TARGETS[@]} -eq 0 ]; then
    echo "Usage: $0 <file-or-dir> [--verify]"
    exit 1
fi

# Collect .lisp files
FILES=()
for target in "${TARGETS[@]}"; do
    if [ -d "$target" ]; then
        for f in "$target"/*.lisp; do
            [ -f "$f" ] && FILES+=("$f")
        done
    elif [ -f "$target" ]; then
        FILES+=("$target")
    else
        echo "Error: $target not found"
        exit 1
    fi
done

if [ ${#FILES[@]} -eq 0 ]; then
    echo "No .lisp files found"
    exit 1
fi

# Convert book name to PascalCase module name
book_to_module() {
    local base
    base=$(basename "$1" .lisp)
    # Split on hyphens, capitalize each part, join
    echo "$base" | sed 's/-/ /g' | awk '{for(i=1;i<=NF;i++) $i=toupper(substr($i,1,1)) substr($i,2)}1' | tr -d ' '
}

mkdir -p "$OUTDIR"

echo "=== Translating ${#FILES[@]} file(s) ==="
TRANSLATED=()
for f in "${FILES[@]}"; do
    module=$(book_to_module "$f")
    outfile="$OUTDIR/$module.lean"
    echo "  $f -> $outfile"
    lake exe acl2lean translate "$f" 2>/dev/null > "$outfile"
    TRANSLATED+=("$outfile")
done

echo ""
echo "=== Generated files ==="
for f in "${TRANSLATED[@]}"; do
    echo "  $f"
done

if [ "$VERIFY" = true ]; then
    echo ""
    echo "=== Verifying with lake build ==="
    # Build all translated modules via lake (handles dependencies)
    output=$(lake build 2>&1)
    PASS=0
    FAIL=0
    for f in "${TRANSLATED[@]}"; do
        # Convert file path to module name: ACL2Lean/Translated/Foo.lean -> ACL2Lean.Translated.Foo
        module=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
        if echo "$output" | grep -q "error.*$module\|$f.*error"; then
            echo "  ✗ $f"
            echo "$output" | grep "$f" | grep "error" | head -3 | sed 's/^/    /'
            FAIL=$((FAIL + 1))
        else
            echo "  ✓ $f"
            PASS=$((PASS + 1))
        fi
    done
    # Also check for any build errors not tied to a specific file
    total_errors=$(echo "$output" | grep -c "^error:" || true)
    if [ "$total_errors" -gt "$FAIL" ]; then
        echo ""
        echo "  Additional build errors:"
        echo "$output" | grep "^error:" | head -5 | sed 's/^/    /'
        FAIL=$total_errors
    fi
    echo ""
    if [ "$FAIL" = "0" ]; then
        echo "Results: all $PASS file(s) compiled successfully"
    else
        echo "Results: $PASS passed, $FAIL failed"
    fi
fi
