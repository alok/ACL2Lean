# Build the project
build:
    lake build

# Run tests
test:
    lake build Tests

# Run the corpus report
report:
    lake exe acl2lean report

# Verify evaluator against ACL2
verify:
    python3 Verify.py

# Translate an ACL2 file to Lean
translate file:
    lake exe acl2lean translate {{file}}

# Evaluate an expression in the context of a file
eval-in file expr:
    lake exe acl2lean eval-in {{file}} "{{expr}}"

# Translate sorting corpus and verify
translate-sorting:
    ./scripts/translate-book.sh acl2_samples/sorting/orderedp.lisp acl2_samples/sorting/how-many.lisp acl2_samples/sorting/perm.lisp acl2_samples/sorting/isort.lisp --verify

# Translate a directory of ACL2 files
translate-dir dir:
    ./scripts/translate-book.sh {{dir}} --verify

# Build ACL2 from the submodule
build-acl2:
    cd acl2 && make LISP=sbcl




















