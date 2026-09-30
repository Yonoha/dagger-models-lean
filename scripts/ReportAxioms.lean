import DaggerModels
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut declarations : Array (String × Json) := #[]
  let mut allAxioms : Array String := #[]
  for (name, _) in env.constants.toList do
    if (`DaggerModels).isPrefixOf name then
      let axioms := (← collectAxioms name).map Name.toString
      declarations := declarations.push (name.toString, toJson (axioms.qsort (· < ·)))
      for ax in axioms do
        unless allAxioms.contains ax do
          allAxioms := allAxioms.push ax
  let report := Json.mkObj [
    ("project_axioms", toJson (allAxioms.qsort (· < ·))),
    ("declarations", Json.mkObj declarations.toList)]
  liftIO <| IO.println report.compress
