# Build the project
build:
    lake build

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




















