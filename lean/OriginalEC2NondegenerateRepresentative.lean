import OriginalEC2NondegenerateOrbit

/-!
# An actual nondegenerate `E_• C₂` simplex in every dimension

The vertex labels of this literal codiscrete-nerve simplex alternate by
reduction modulo two. The previously proved orbit theorem then reaches every
other nondegenerate simplex by the original regular `C₂` action.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2NondegenerateSimplices
open DaggerOriginalEC2NondegenerateOrbit

universe u

namespace DaggerOriginalEC2NondegenerateRepresentative

noncomputable section

/-- The literal alternating-vertex functor into `Codiscrete C2`. -/
def representative (n : ℕ) : ComposableArrows (Codiscrete C2.{u}) n :=
  Codiscrete.functor (fun j : Fin (n + 1) ↦
    ULift.up (Multiplicative.ofAdd ((j.val : ℕ) : ZMod 2)))

private theorem representative_obj (n : ℕ) (j : Fin (n + 1)) :
    ((representative.{u} n).obj j).as =
      ULift.up (Multiplicative.ofAdd ((j.val : ℕ) : ZMod 2)) := rfl

/-- Consecutive labels differ, so the actual representative is nondegenerate. -/
theorem representative_nondegenerate (n : ℕ) :
    representative.{u} n ∈ (simplicialEC2.{u}).nonDegenerate n := by
  apply (nondegenerate_iff_adjacent_labels n (representative n)).2
  intro i heq
  have hh := congrArg (fun z : C2.{u} ↦ Multiplicative.toAdd z.down) heq
  change (i.castSucc.val : ZMod 2) = (i.succ.val : ZMod 2) at hh
  have hcast : (i.val : ZMod 2) = (i.val : ZMod 2) + 1 := by
    simp at hh
  have hzero : (0 : ZMod 2) = 1 := add_left_cancel (by
    simpa only [add_zero] using hcast)
  have hne : (0 : ZMod 2) ≠ 1 := by decide
  exact hne hzero

/-- The original codiscrete nerve has a nondegenerate simplex in every degree. -/
theorem exists_nondegenerate (n : ℕ) :
    ∃ s : ComposableArrows (Codiscrete C2.{u}) n,
      s ∈ (simplicialEC2.{u}).nonDegenerate n :=
  ⟨representative n, representative_nondegenerate n⟩

/-- Every actual nondegenerate simplex lies in this representative's orbit. -/
theorem representative_orbit (n : ℕ)
    (s : ComposableArrows (Codiscrete C2.{u}) n)
    (hs : s ∈ (simplicialEC2.{u}).nonDegenerate n) :
    ∃ g : C2.{u},
      ((simplicialAction.{u}.ρ g).asHom).app (op ⦋n⦌)
        (representative.{u} n) = s :=
  nondegenerate_orbit_transitive n (representative n) s
    (representative_nondegenerate n) hs

end

end DaggerOriginalEC2NondegenerateRepresentative
