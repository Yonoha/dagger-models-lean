import OriginalHomotopyCategoryUnitEdges

/-!
# Actual inverse-edge representatives for the original unit-preimage core

The exact original unit formula identifies edge invertibility with invertibility
of its original path class. Edge representability in that same path quotient
then supplies a reversed edge whose path class is the inverse. Its endpoints,
unit and core membership are unchanged. Triangle witnesses remain separate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryPathEdgeRepresentatives
open DaggerOriginalHomotopyCategoryUnitEdges

universe u

namespace DaggerOriginalQuasicategoryInverseEdgeRepresentatives

noncomputable section

/-- Original unit invertibility is precisely invertibility of the same original edge path class. -/
theorem edgeIsInvertible_iff_original_homMk_isIso (X : SSet.{u})
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    edgeIsInvertible X e.edge ↔ IsIso (SSet.Truncated.HomotopyCategory.homMk e) := by
  have h := congrArg
    (fun t : ComposableArrows (SSet.hoFunctor.obj X) 1 ↦ IsIso t.hom)
    (original_unit_app_edge X e)
  exact Iff.of_eq h

/-- An invertible original edge has an actual inverse-edge representative with fixed endpoints. -/
theorem original_inverse_edge (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) (he : edgeIsInvertible X e.edge) :
    ∃ r : SSet.Edge y x,
      SSet.Truncated.HomotopyCategory.homMk e ≫
        SSet.Truncated.HomotopyCategory.homMk r = 𝟙 _ ∧
      SSet.Truncated.HomotopyCategory.homMk r ≫
        SSet.Truncated.HomotopyCategory.homMk e = 𝟙 _ ∧ edgeIsInvertible X r.edge := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    (edgeIsInvertible_iff_original_homMk_isIso X e).mp he
  obtain ⟨r, hr⟩ := original_homMk_surjective X hX
    (inv (SSet.Truncated.HomotopyCategory.homMk e))
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [hr]
    exact IsIso.hom_inv_id _
  · rw [hr]
    exact IsIso.inv_hom_id _
  · apply (edgeIsInvertible_iff_original_homMk_isIso X r).mpr
    rw [hr]
    infer_instance

/-- Every original core edge admits a reversed edge in the same core representing its inverse. -/
theorem core_inverse_edge (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y)
    (he : e.edge ∈ (ordinaryCoreCandidate X).obj (op ⦋1⦌)) :
    ∃ r : SSet.Edge y x, r.edge ∈ (ordinaryCoreCandidate X).obj (op ⦋1⦌) ∧
      SSet.Truncated.HomotopyCategory.homMk e ≫
        SSet.Truncated.HomotopyCategory.homMk r = 𝟙 _ ∧
      SSet.Truncated.HomotopyCategory.homMk r ≫
        SSet.Truncated.HomotopyCategory.homMk e = 𝟙 _ := by
  obtain ⟨r, her, hre, hr⟩ := original_inverse_edge X hX e
    ((mem_ordinaryCoreCandidate_one_iff X e.edge).mp he)
  exact ⟨r, (mem_ordinaryCoreCandidate_one_iff X r.edge).mpr hr, her, hre⟩

end

end DaggerOriginalQuasicategoryInverseEdgeRepresentatives
