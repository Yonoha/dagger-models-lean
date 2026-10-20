import ActualQRealizationCommonVertexFaces
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-! Every literal Kan horn inclusion is a trivial cofibration under the original Q realization. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra Simplicial
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualQRealizationCommonVertexFaces DaggerActualQRealizationFaceUnionGluing
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQRealizationHornWeakness

noncomputable section

/-- The actual horn is the union of every codimension-one face containing its selected vertex. -/
theorem horn_eq_faceUnion (n : ℕ) (i : Fin (n + 2)) :
    SSet.horn.{u} (n + 1) i = faceUnion.{u}
      (Finset.univ : Finset {j : Fin (n + 2) // j ≠ i}) (fun j ↦ {j.val}ᶜ) := by
  simp only [SSet.horn_eq_iSup, faceUnion, Finset.sup_eq_iSup,
    Finset.mem_univ, iSup_true]
  apply le_antisymm
  · refine iSup_le fun j ↦ ?_
    exact le_iSup_of_le
      (⟨j.val, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using j.property⟩ :
        {j : Fin (n + 2) // j ≠ i}) le_rfl
  · refine iSup_le fun j ↦ ?_
    exact le_iSup_of_le
      (⟨j.val, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using j.property⟩ :
        ({i}ᶜ : Set (Fin (n + 2)))) le_rfl

/-- All positive-dimensional horns have weak terminal collapse under the actual realization. -/
theorem horn_toUnit_GW (n : ℕ) (i : Fin (n + 2)) :
    GW (toUnit (realization.{u}.obj (SSet.horn.{u} (n + 1) i).toSSet)) := by
  classical
  have hother : ∃ j : Fin (n + 2), j ≠ i := by
    by_cases hi : i = 0
    · refine ⟨1, ?_⟩
      rw [hi]
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv
    · exact ⟨0, Ne.symm hi⟩
  obtain ⟨j, hj⟩ := hother
  have hs : (Finset.univ : Finset {j : Fin (n + 2) // j ≠ i}).Nonempty :=
    ⟨⟨j, hj⟩, Finset.mem_univ _⟩
  have ha : ∀ j ∈ (Finset.univ : Finset {j : Fin (n + 2) // j ≠ i}),
      i ∈ ({j.val}ᶜ : Finset (Fin (n + 2))) := by
    intro k _
    simpa only [Finset.mem_compl, Finset.mem_singleton] using Ne.symm k.property
  rw [horn_eq_faceUnion]
  exact faceUnion_toUnit_GW _ _ i hs ha

/-- The exact original realization sends every actual Kan horn inclusion to a weak map. -/
theorem horn_inclusion_GW (n : ℕ) (i : Fin (n + 2)) :
    GW (realization.{u}.map (SSet.horn.{u} (n + 1) i).ι) :=
  map_GW_of_collapses _ (horn_toUnit_GW n i)
    (DaggerActualQRealizationRepresentableWeakness.representable_toUnit_GW ⦋n + 1⦌)

/-- Every such image is a trivial cofibration in the actual Kan-Quillen model. -/
theorem horn_trivialCofibration (n : ℕ) (i : Fin (n + 2)) :
    trivialCofibrations SSet.{u} (realization.{u}.map (SSet.horn.{u} (n + 1) i).ι) := by
  letI : Cofibration (SSet.horn.{u} (n + 1) i).ι :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  letI : WeakEquivalence (realization.{u}.map (SSet.horn.{u} (n + 1) i).ι) :=
    (weakEquivalence_iff_GW _).2 (horn_inclusion_GW n i)
  exact mem_trivialCofibrations _

end
end DaggerActualQRealizationHornWeakness
