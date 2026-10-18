import OriginalCounitRightConeQRealizationAdjunctionReconciled
import SSetGluing
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-! Weak reflection and a common weak target for the unchanged original-Q singular complex. -/

set_option autoImplicit false
open CategoryTheory DaggerSSetGluing
open DaggerOriginalCounitRightConeQRealizationAdjunction
universe u

namespace DaggerActualQSingularWeakReflectionChallenge

def statement : Prop :=
  (∀ X Y : SSet.{u}, X.KanComplex → Y.KanComplex →
    ∀ f : X ⟶ Y, GW (singular.{u}.map f) ↔ GW f) ∧
  ∀ X : SSet.{u}, X.KanComplex →
    ∃ Z : SSet.{u}, ∃ i : X ⟶ Z, ∃ j : singular.{u}.obj X ⟶ Z, GW i ∧ GW j

end DaggerActualQSingularWeakReflectionChallenge
