import OriginalFixedObjectStrictDaggerSmallObject

/-!
# The native model structure on the exact original fixed-object strict dagger groupoids

All finite limits, finite colimits, closure, lifting and both factorizations are now proved.
The weak and fibration classes are exactly the original Homwise simplicial classes.
This does not establish the simplicial model axioms or the whole of main theorem C.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalFixedObjectStrictDaggerModel
noncomputable section

/-- Unconditional native model category on the original same-O strict dagger groupoids. -/
scoped instance strictDaggerModel (O : Type u) : ModelCategory (FixedStrictDaggerGroupoids O) :=
  DaggerOriginalFixedObjectColimitModelRecognition.strictDaggerModelFromFactorization O

/-- The model weak equivalences are exactly the weak equivalences on every original Hom. -/
theorem model_weakEquivalence_iff {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) : WeakEquivalence F ↔
      ∀ x y : O, WeakEquivalence (F.hom.underlying.map x y) :=
  DaggerOriginalFixedObjectGroupoidClasses.strictDagger_weakEquivalence_iff F

/-- The model fibrations are exactly the fibrations on every original Hom. -/
theorem model_fibration_iff {O : Type u} {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    Fibration F ↔ ∀ x y : O, Fibration (F.hom.underlying.map x y) :=
  DaggerOriginalFixedObjectGroupoidClasses.strictDagger_fibration_iff F

/-- The model cofibrations use precisely the intended trivial-fibration left lifting class. -/
theorem model_cofibration_iff {O : Type u} {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    Cofibration F ↔
      (DaggerOriginalFixedObjectGroupoidClasses.strictDaggerFibrations O ⊓
        DaggerOriginalFixedObjectGroupoidClasses.strictDaggerWeakEquivalences O).llp F := by
  rw [cofibration_iff F]
  rfl

end
end DaggerOriginalFixedObjectStrictDaggerModel
