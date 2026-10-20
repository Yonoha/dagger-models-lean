import DaggerModels
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every compiled declaration in the DaggerModels namespace, including
definitions and generated declarations, using Lean's axiom collector.
Only the three standard foundational axioms are allowed.
-/

open Lean Elab Command

elab "#audit_dagger_models" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`DaggerModels).isPrefixOf name then
      count := count + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
  if count == 0 then
    throwError "No DaggerModels declarations were found; the audit would be empty."
  logInfo m!"Axiom audit passed for {count} declarations. Allowed: {allowed}."

#audit_dagger_models
