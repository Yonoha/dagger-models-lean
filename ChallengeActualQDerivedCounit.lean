import OriginalCounitRightConeQRealizationAdjunctionReconciled
import SSetGluing
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! Literal original-Q counit invertibility and the universal right derived equivalence. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQDerivedCounitChallenge

def statement : Prop :=
  (∀ X : SSet.{u}, X.KanComplex →
    IsIso ((weakEquivalences SSet.{u}).Q.map
      (realizationSingularAdjunction.counit.app X))) ∧
  let W := (weakEquivalences SSet.{u}ᵒᵖ).op
  let L := (weakEquivalences SSet.{u}).Q
  ∃ R : W.Localization ⥤ (weakEquivalences SSet.{u}).Localization,
    ∃ β : (opOpEquivalence SSet.{u}).functor ⋙ singular.{u} ⋙ L ⟶ W.Q ⋙ R,
      R.IsRightDerivedFunctor β W ∧ R.IsEquivalence ∧
        ∀ X : SSet.{u}, X.KanComplex → IsIso (β.app (op (op X)))

end DaggerActualQDerivedCounitChallenge
