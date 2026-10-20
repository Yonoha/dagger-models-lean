import OriginalEC2BorelCofibrancy

/-!
# Identification of the exact underlying Borel right class

The retained topological q-model has the realized simplex boundaries as its
cofibration generators. Its existing recognition theorem identifies their
right lifting class with its trivial fibrations. No action model structure or
comparison with the compactly generated weak Hausdorff category is assumed.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2BorelCofibrancy

universe u

namespace DaggerOriginalEC2BorelModelCompatibility

/-- The right class is exactly underlying trivial fibrations in the retained
TopCat model, not an extra hypothesis imposed on the target object. -/
theorem borelTrivialFibrations_eq : borelTrivialFibrations.{u} =
    (trivialFibrations TopCat.{u}).inverseImage (Action.forget TopCat.{u} C2.{u}) := by
  unfold borelTrivialFibrations
  have h : TopCat.modelCategory.I.rlp = trivialFibrations TopCat.{u} :=
    TopCat.modelCategory.packageTopCat.I_rlp_eq_trivialFibrations
  rw [h]

/-- Membership states exactly fibration and weak equivalence of the original
underlying equivariant map, using the retained TopCat model. -/
theorem borelTrivialFibrations_iff {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    borelTrivialFibrations.{u} p ↔ Fibration p.hom ∧ WeakEquivalence p.hom := by
  rw [borelTrivialFibrations_eq]
  exact mem_trivialFibrations_iff p.hom

end DaggerOriginalEC2BorelModelCompatibility
