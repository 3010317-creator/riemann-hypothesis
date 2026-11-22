import Lean

/-!
Prints every token of the parser's token table after importing the given modules and activating
the scoped syntax of every namespace, one token per line. This is a superset of the tokens that
can be active in any one file.

usage: lean --run DumpTokens.lean MODULE...
-/

open Lean

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  let env ← importModules (args.toArray.map fun m => { module := m.toName }) {} (loadExts := true)
  -- Every namespace that can hold scoped syntax is a prefix of the name of some declaration.
  let namespaces := env.constants.fold (init := ({} : NameSet)) fun acc n _ => Id.run do
    let mut acc := acc
    let mut p := n.getPrefix
    while !p.isAnonymous && !acc.contains p do
      acc := acc.insert p
      p := p.getPrefix
    return acc
  let mut env := env
  for ns in namespaces.toList do
    env := Parser.parserExtension.activateScoped env ns
  let out ← IO.getStdout
  for token in (Parser.getTokenTable env).findPrefix "" do
    out.putStrLn token
