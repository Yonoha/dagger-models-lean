import OriginalFixedObjectStrictActionModel
import TopCatModelCategory.QuillenAdjunction

/-!
# The actual original fixed-object dagger/action Quillen equivalence

Both models have been constructed with the exact original weak and fibration classes.
The full equivalence preserves cofibrations and its inverse preserves fibrations.
Its original unit is an isomorphism, so the actual full adjunction Hom equivalence
preserves and detects weak equivalences, even without cofibrancy/fibrancy restrictions.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDaggerActionEquivalence DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalFixedObjectStrictActionClasses DaggerOriginalEquivalenceFactorizationTransport
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictModel DaggerOriginalFixedObjectStrictDaggerModel
  DaggerOriginalFixedObjectStrictActionClasses DaggerOriginalFixedObjectStrictActionModel
universe u
namespace DaggerOriginalFixedObjectDaggerActionQuillenEquivalence
noncomputable section

/-- The full inverse equivalence preserves and detects the intended projective weak class. -/
theorem inverse_weakEquivalence_iff {O : Type u}
    {X Y : Action (FixedStrictGroupoids O) C2.{u}} (p : X ⟶ Y) :
    WeakEquivalence ((fixedDaggerActionEquivalence O).inverse.map p) ↔ WeakEquivalence p := by
  rw [weakEquivalence_iff, weakEquivalence_iff]
  change weakEquivalences (FixedStrictDaggerGroupoids O)
    ((fixedDaggerActionEquivalence O).inverse.map p) ↔ projectiveWeakEquivalences O p
  rw [projectiveWeak_eq_inverse]
  rfl

/-- The complete original forward comparison preserves the original canonical cofibrations. -/
theorem functor_cofibration {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) (hF : Cofibration F) :
    Cofibration ((fixedDaggerActionEquivalence O).functor.map F) := by
  apply (cofibration_iff _).2
  change cofibrations (FixedStrictDaggerGroupoids O)
    ((fixedDaggerActionEquivalence O).inverse.map
      ((fixedDaggerActionEquivalence O).functor.map F))
  exact (map_inverse_iff (fixedDaggerActionEquivalence O).symm
    (cofibrations (FixedStrictDaggerGroupoids O)) F).2 ((cofibration_iff F).1 hF)

/-- The full inverse comparison preserves the exact original Homwise fibrations. -/
theorem inverse_fibration {O : Type u}
    {X Y : Action (FixedStrictGroupoids O) C2.{u}} (p : X ⟶ Y) (hp : Fibration p) :
    Fibration ((fixedDaggerActionEquivalence O).inverse.map p) := by
  apply (fibration_iff _).2
  have h := (fibration_iff p).1 hp
  change projectiveFibrations O p at h
  rw [projectiveFib_eq_inverse] at h
  exact h

/-- The full original dagger/action adjunction is native Quillen for the proved models. -/
theorem daggerAction_isQuillen (O : Type u) :
    (fixedDaggerActionEquivalence O).toAdjunction.IsQuillenAdjunction where
  cofibration_map i := functor_cofibration i inferInstance
  fibration_map p := inverse_fibration p inferInstance

/-- The actual full adjunction Hom equivalence preserves and detects weak equivalences. -/
theorem homEquiv_weakEquivalence_iff {O : Type u} (A : FixedStrictDaggerGroupoids O)
    (X : Action (FixedStrictGroupoids O) C2.{u})
    (f : (fixedDaggerActionEquivalence O).functor.obj A ⟶ X) :
    WeakEquivalence (((fixedDaggerActionEquivalence O).toAdjunction.homEquiv A X) f) ↔
      WeakEquivalence f := by
  rw [Adjunction.homEquiv_unit, Equivalence.toAdjunction_unit]
  change WeakEquivalence ((fixedDaggerActionEquivalence O).unitIso.hom.app A ≫
    (fixedDaggerActionEquivalence O).inverse.map f) ↔ WeakEquivalence f
  calc
    WeakEquivalence ((fixedDaggerActionEquivalence O).unitIso.hom.app A ≫
        (fixedDaggerActionEquivalence O).inverse.map f) ↔
        WeakEquivalence ((fixedDaggerActionEquivalence O).inverse.map f) := by
      rw [weakEquivalence_iff, weakEquivalence_iff]
      exact (weakEquivalences (FixedStrictDaggerGroupoids O)).cancel_left_of_respectsIso _ _
    _ ↔ WeakEquivalence f := inverse_weakEquivalence_iff f

/-- The original dagger groupoid and full projective C2 action models are Quillen equivalent. -/
theorem daggerAction_isQuillenEquivalence (O : Type u) :
    (fixedDaggerActionEquivalence O).toAdjunction.IsQuillenEquivalence where
  toIsQuillenAdjunction := daggerAction_isQuillen O
  weakEquivalence_homEquiv_iff f := homEquiv_weakEquivalence_iff _ _ f

end
end DaggerOriginalFixedObjectDaggerActionQuillenEquivalence
