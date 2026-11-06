import MiniLean.Examples

def main : IO Unit := do
  IO.println "MiniLean proof checker"
  IO.println s!"Identity proof accepted: {MiniLean.check (.imp (.atom 0) (.atom 0)) MiniLean.Examples.identity}"
