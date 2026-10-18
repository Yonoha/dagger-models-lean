import OriginalBorelFreeGenerators

/-!
# Native realization of original simplicial monomorphisms

Mathlib's simplicial cofibration class and the existing realization-singular
lifting correspondence prove that every original simplicial monomorphism
realizes to a native TopCat cofibration, in every universe. No action
cofibration conclusion is inferred merely from an underlying cofibration.
-/

set_option autoImplicit false

open CategoryTheory MorphismProperty HomotopicalAlgebra
open scoped TopCat.modelCategory SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalRealizationMonomorphismCofibrations

/-- Every original simplicial monomorphism realizes to a native topological cofibration. -/
theorem realization_map_mono_cofibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    Cofibration (SSet.toTop.map i) := by
  rw [HomotopicalAlgebra.cofibration_iff]
  intro X Y p hp
  rw [sSetTopAdj.hasLiftingProperty_iff]
  have hsing : SSet.modelCategoryQuillen.I.rlp (TopCat.toSSet.map p) :=
    (TopCat.modelCategory.rlp_I_iff p).1 hp
  rw [SSet.modelCategoryQuillen.I_rlp_eq_monomorphisms_rlp] at hsing
  exact hsing i (monomorphisms.infer_property i)

end DaggerOriginalRealizationMonomorphismCofibrations
