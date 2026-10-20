import OriginalEquivalenceFactorizationTransport
import TopCatModelCategory.QuillenAdjunction

/-! Native Quillen equivalence with each target class exactly the source inverse-image class. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalEquivalenceFactorizationTransport
universe u v a b
namespace DaggerOriginalEquivalenceQuillenTransport
noncomputable section
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]
variable [ModelCategory C] [ModelCategory D]

/-- Exact inverse-image classes make the full equivalence a native Quillen equivalence. -/
theorem isQuillenEquivalence (E : C ≌ D)
    (hw : weakEquivalences D = (weakEquivalences C).inverseImage E.inverse)
    (hf : fibrations D = (fibrations C).inverseImage E.inverse)
    (hc : cofibrations D = (cofibrations C).inverseImage E.inverse) :
    E.toAdjunction.IsQuillenEquivalence := by
  have hinv : ∀ {X Y : D} (p : X ⟶ Y),
      WeakEquivalence (E.inverse.map p) ↔ WeakEquivalence p := by
    intro X Y p
    rw [weakEquivalence_iff, weakEquivalence_iff, hw]
    rfl
  refine
    { cofibration_map := ?_
      fibration_map := ?_
      weakEquivalence_homEquiv_iff := ?_ }
  · intro A B i hi
    apply (cofibration_iff _).2
    rw [hc]
    exact (map_inverse_iff E.symm (cofibrations C) i).2 ((cofibration_iff i).1 hi)
  · intro X Y p hp
    apply (fibration_iff _).2
    have h := (fibration_iff p).1 hp
    rw [hf] at h
    exact h
  · intro A X _ _ f
    rw [Adjunction.homEquiv_unit, Equivalence.toAdjunction_unit]
    change WeakEquivalence (E.unitIso.hom.app A ≫ E.inverse.map f) ↔ WeakEquivalence f
    calc
      WeakEquivalence (E.unitIso.hom.app A ≫ E.inverse.map f) ↔
          WeakEquivalence (E.inverse.map f) := by
        rw [weakEquivalence_iff, weakEquivalence_iff]
        exact (weakEquivalences C).cancel_left_of_respectsIso _ _
      _ ↔ WeakEquivalence f := hinv f

end
end DaggerOriginalEquivalenceQuillenTransport
