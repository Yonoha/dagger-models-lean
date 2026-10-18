import Lean

/-! Concatenate fixed source string chunks into one ordinary literal expression. -/

open Lean Elab Term

/-- Keep large literal datasets readable without changing their decoded text. -/
elab "recovered_literal_chunks%" "[" pieces:str,* "]" : term => do
  return mkStrLit (String.join (pieces.getElems.toList.map (·.getString)))
