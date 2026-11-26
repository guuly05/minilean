import MiniLean.Source

def main (args : List String) : IO Unit := do
  if args == ["--help"] || args == ["-h"] then
    IO.println "Usage: minilean <file>"
    IO.println "Check theorem declarations in a MiniLean source file."
  else
    match args with
    | [path] =>
        let contents ← IO.FS.readFile path
        match MiniLean.checkSource contents with
        | .error err =>
            IO.eprintln s!"{path}:{err.position.line}:{err.position.column}: error: {err.message}"
            throw (IO.Error.userError "source check failed")
        | .ok results =>
            let mut rejected := false
            for result in results do
              if result.accepted then
                IO.println s!"{result.name}: accepted"
              else
                IO.eprintln s!"{result.name}: rejected"
                rejected := true
            if rejected then throw (IO.Error.userError "one or more theorems were rejected")
    | _ =>
        IO.eprintln "Usage: minilean <file> (or --help)"
        throw (IO.Error.userError "invalid command line")
