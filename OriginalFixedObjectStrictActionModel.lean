import OriginalFixedObjectStrictActionClasses
import OriginalEquivalenceModelTransport

/-!
# The actual projective model on actions of original fixed-object strict groupoids

The weak and fibration classes were defined by the unchanged underlying ordinary maps.
The original dagger/action equivalence and the proved source dagger model supply all
native model axioms. The transported cofibrations are proved to be exactly the canonical
left lifting class against underlying original trivial fibrations.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalFixedObjectDaggerActionEquivalence
open DaggerOriginalFixedObjectStrictActionClasses
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictModel DaggerOriginalFixedObjectStrictDaggerModel
  DaggerOriginalFixedObjectStrictActionClasses SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalFixedObjectStrictActionModel
noncomputable section

/-- Unconditional native projective model on the full original fixed-object C2 action category. -/
scoped instance projectiveModel (O : Type u) :
    ModelCategory (Action (FixedStrictGroupoids O) C2.{u}) :=
  DaggerOriginalEquivalenceModelTransport.transportModel (fixedDaggerActionEquivalence O).symm
    (projectiveWeak_eq_inverse O) (projectiveFib_eq_inverse O) rfl

open scoped DaggerOriginalFixedObjectStrictActionModel

/-- Native projective cofibrations are exactly the canonical underlying-trivial-fibration LLP. -/
theorem projectiveCof_eq_llp (O : Type u) :
    cofibrations (Action (FixedStrictGroupoids O) C2.{u}) =
      (trivialFibrations (Action (FixedStrictGroupoids O) C2.{u})).llp := by
  have h : cofibrations (Action (FixedStrictGroupoids O) C2.{u}) ≤
      (trivialFibrations (Action (FixedStrictGroupoids O) C2.{u})).llp := by
    intro A B i hi X Y p hp
    haveI : Cofibration i := (cofibration_iff i).2 hi
    haveI : Fibration p := ((mem_trivialFibrations_iff p).1 hp).1
    haveI : WeakEquivalence p := ((mem_trivialFibrations_iff p).1 hp).2
    infer_instance
  exact (MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts h).symm

/-- Projective cofibrations use precisely the specified original underlying right class. -/
theorem cofibration_iff_original {O : Type u}
    {X Y : Action (FixedStrictGroupoids O) C2.{u}} (p : X ⟶ Y) :
    Cofibration p ↔ ((trivialFibrations (FixedStrictGroupoids O)).inverseImage
      (Action.forget (FixedStrictGroupoids O) C2.{u})).llp p := by
  rw [cofibration_iff, projectiveCof_eq_llp]
  rfl

/-- Projective weak equivalences retain the exact simplicial weak class on every original Hom. -/
theorem weakEquivalence_iff_original {O : Type u}
    {X Y : Action (FixedStrictGroupoids O) C2.{u}} (p : X ⟶ Y) :
    WeakEquivalence p ↔ ∀ x y : O, WeakEquivalence (p.hom.hom.map x y) := by
  rw [weakEquivalence_iff_underlying]
  exact DaggerOriginalFixedObjectGroupoidClasses.strict_weakEquivalence_iff p.hom

/-- Projective fibrations retain the exact simplicial fibration class on every original Hom. -/
theorem fibration_iff_original {O : Type u}
    {X Y : Action (FixedStrictGroupoids O) C2.{u}} (p : X ⟶ Y) :
    Fibration p ↔ ∀ x y : O, Fibration (p.hom.hom.map x y) := by
  rw [fibration_iff_underlying]
  exact DaggerOriginalFixedObjectGroupoidClasses.strict_fibration_iff p.hom

end
end DaggerOriginalFixedObjectStrictActionModel
