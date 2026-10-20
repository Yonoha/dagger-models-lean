import OriginalEC2NondegenerateRepresentative

/-!
# One actual free `C₂` orbit of nondegenerate simplices in every degree

The orbit map uses the original regular action on the actual codiscrete nerve.
Its bijectivity is simplicial; equivariant skeletal pushouts and topological
free-CW claims are separate later constructions.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2NondegenerateSimplices
open DaggerOriginalEC2NondegenerateOrbit
open DaggerOriginalEC2NondegenerateRepresentative

universe u

namespace DaggerOriginalEC2NondegenerateFreeOrbit

noncomputable section

/-- The actual regular action preserves nondegeneracy in each simplicial degree. -/
theorem action_nondegenerate (g : C2.{u}) (n : ℕ)
    (s : ComposableArrows (Codiscrete C2.{u}) n)
    (hs : s ∈ (simplicialEC2.{u}).nonDegenerate n) :
    ((simplicialAction.{u}.ρ g).asHom).app (op ⦋n⦌) s ∈
      (simplicialEC2.{u}).nonDegenerate n := by
  apply (nondegenerate_iff_adjacent_labels n _).2
  intro i heq
  have hmul : g * (s.obj i.castSucc).as =
      g * (s.obj i.succ).as := by
    simpa only [action_obj] using heq
  exact ((nondegenerate_iff_adjacent_labels n s).1 hs i)
    (mul_left_cancel hmul)

/-- The orbit of the literal alternating representative, valued in actual
nondegenerate simplices of `nerve (Codiscrete C2)`. -/
def orbitMap (n : ℕ) (g : C2.{u}) :
    {s : ComposableArrows (Codiscrete C2.{u}) n //
      s ∈ (simplicialEC2.{u}).nonDegenerate n} :=
  ⟨((simplicialAction.{u}.ρ g).asHom).app (op ⦋n⦌)
      (representative.{u} n),
    action_nondegenerate g n (representative n) (representative_nondegenerate n)⟩

/-- First-vertex cancellation proves injectivity; the representative-orbit
theorem proves surjectivity, for the same actual action. -/
theorem orbitMap_bijective (n : ℕ) : Function.Bijective (orbitMap.{u} n) := by
  constructor
  · intro g h heq
    have hzero := congrArg
      (fun z : {s : ComposableArrows (Codiscrete C2.{u}) n //
          s ∈ (simplicialEC2.{u}).nonDegenerate n} ↦ (z.val.obj 0).as) heq
    change g * ((representative.{u} n).obj 0).as =
      h * ((representative.{u} n).obj 0).as at hzero
    exact mul_right_cancel hzero
  · rintro ⟨s, hs⟩
    obtain ⟨g, hg⟩ := representative_orbit n s hs
    exact ⟨g, Subtype.ext hg⟩

/-- Exactly one actual free `C₂` orbit of nondegenerate `n`-simplices. -/
def nondegenerateEquiv (n : ℕ) :
    C2.{u} ≃ {s : ComposableArrows (Codiscrete C2.{u}) n //
      s ∈ (simplicialEC2.{u}).nonDegenerate n} :=
  Equiv.ofBijective (orbitMap n) (orbitMap_bijective n)

end

end DaggerOriginalEC2NondegenerateFreeOrbit
