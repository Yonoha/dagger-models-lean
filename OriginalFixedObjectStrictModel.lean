import OriginalFixedObjectOrdinaryFactorizationTransfer

/-!
# The native model structure on the exact original fixed-object strict groupoids

The full ordinary canonical cofibration/trivial-fibration factorization has been
constructed from the original dagger factorization. All native model axioms now
follow from the proved finite limits, finite colimits, closure, acyclicity and
mapping-path factorization. This does not assert the simplicial model axioms.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalFixedObjectStrictModel
noncomputable section

/-- Unconditional native model category on the original same-O strict groupoids. -/
scoped instance strictModel (O : Type u) : ModelCategory (FixedStrictGroupoids O) :=
  DaggerOriginalFixedObjectColimitModelRecognition.strictModelFromFactorization O

/-- Weak equivalences are exactly native weak equivalences on every unchanged original Hom. -/
theorem model_weakEquivalence_iff {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    WeakEquivalence F ↔ ∀ x y : O, WeakEquivalence (F.hom.map x y) :=
  DaggerOriginalFixedObjectGroupoidClasses.strict_weakEquivalence_iff F

/-- Fibrations are exactly native fibrations on every unchanged original Hom. -/
theorem model_fibration_iff {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    Fibration F ↔ ∀ x y : O, Fibration (F.hom.map x y) :=
  DaggerOriginalFixedObjectGroupoidClasses.strict_fibration_iff F

/-- Cofibrations are precisely the intended original trivial-fibration LLP class. -/
theorem model_cofibration_iff {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    Cofibration F ↔
      (DaggerOriginalFixedObjectGroupoidClasses.strictFibrations O ⊓
        DaggerOriginalFixedObjectGroupoidClasses.strictWeakEquivalences O).llp F := by
  rw [cofibration_iff F]
  rfl

end
end DaggerOriginalFixedObjectStrictModel
