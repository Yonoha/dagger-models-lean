import ActualQRealizationHornWeakness
import TopCatModelCategory.QuillenAdjunction

/-! The literal original-Q realization-singular adjunction is Kan-Quillen. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualQRealizationHornWeakness
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQRealizationQuillen

noncomputable section

/-- Fibrations lift against every actual realized generating horn inclusion. -/
theorem realization_horn_lifting {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
    (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty (realization.{u}.map (SSet.horn.{u} (n + 1) i).ι) p := by
  have h := horn_trivialCofibration.{u} n i
  rw [mem_trivialCofibrations_iff] at h
  letI : Cofibration (realization.{u}.map (SSet.horn.{u} (n + 1) i).ι) := h.1
  letI : WeakEquivalence (realization.{u}.map (SSet.horn.{u} (n + 1) i).ι) := h.2
  infer_instance

/-- Transfer the literal horn lifting problem through the unchanged actual adjunction. -/
theorem singular_horn_lifting {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
    (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty (SSet.horn.{u} (n + 1) i).ι (singular.{u}.map p) :=
  (realizationSingularAdjunction.{u}.hasLiftingProperty_iff
    (SSet.horn.{u} (n + 1) i).ι p).mp (realization_horn_lifting p n i)

/-- The native generating-horn description shows that singular preserves every fibration. -/
theorem singular_fibration {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p] :
    Fibration (singular.{u}.map p) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  intro A B j hj
  change (⨆ n : ℕ, MorphismProperty.ofHoms
    (fun i : Fin (n + 2) ↦ (SSet.horn.{u} (n + 1) i).ι)) j at hj
  rw [MorphismProperty.iSup_iff] at hj
  obtain ⟨n, hn⟩ := hj
  cases hn with
  | mk i => exact singular_horn_lifting p n i

instance singular_preservesFibrations : singular.{u}.PreservesFibrations where
  fibration_map p := singular_fibration p

instance realization_preservesTrivialCofibrations :
    realization.{u}.PreservesTrivialCofibrations :=
  realizationSingularAdjunction.{u}.preservesTrivialCofibrations_iff_preservesFibrations.2
    inferInstance

/-- The actual left Kan extension and actual singular functor form a Quillen adjunction. -/
theorem isQuillen : realizationSingularAdjunction.{u}.IsQuillenAdjunction := ⟨⟩

end
end DaggerActualQRealizationQuillen
