import ACL2Lean

def main : IO Unit := do
  IO.println "ACL2 to Lean 4 Bridge - Corpus Report"
  ACL2.reportSamples
