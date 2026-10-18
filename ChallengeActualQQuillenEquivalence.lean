import OriginalCounitBNextConeRealizationFactorizationReconciled
import SSetGluing
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import TopCatModelCategory.QuillenAdjunction

/-! The problem states the unchanged original maps, independently of the new solution. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite Simplicial EnrichedCategory
open DaggerOriginalCounitRightConeQRealizationAdjunction DaggerSSetGluing
open DaggerOriginalCounitBNextConeRealizationFactorization
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQQuillenEquivalenceChallenge

def statement : Prop :=
  (∀ (X Y : SSet.{u}) (f : X ⟶ Y), GW (realization.map f) ↔ GW f) ∧
  (∀ X : SSet.{u}, X.KanComplex →
    GW (realizationSingularAdjunction.counit.app X)) ∧
  realizationSingularAdjunction.{u}.IsQuillenEquivalence ∧
  ∀ D : DaggerModels.SimplicialCat.{u, u},
    (∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y)) →
    ∀ v w : (DaggerModels.OrdinaryRigidification.coherentNerve.obj D).obj (op ⦋0⦌),
      GW (coneEvaluationMap D v w)

end DaggerActualQQuillenEquivalenceChallenge
