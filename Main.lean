import «CS»
import «IR»

open IR.Chapter1

set_option maxRecDepth 100000 in
#time def test := Chapter1.words₁ Chapter1.sonnet18

def main : IO Unit := do
  let ls ← dhbb (Query.and (Query.w "senadores") (Query.w "votos"))
  IO.println ls
