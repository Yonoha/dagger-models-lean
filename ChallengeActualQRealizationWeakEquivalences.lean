import OriginalCounitRightConeQRealizationAdjunctionReconciled
import SSetGluing

/-! Preservation of every actual geometric weak equivalence, in all universes. -/

set_option autoImplicit false
open CategoryTheory DaggerSSetGluing
open DaggerOriginalCounitRightConeQRealizationAdjunction
universe u

namespace DaggerActualQRealizationWeakEquivalencesChallenge

def statement : Prop :=
  ∀ X Y : SSet.{u}, ∀ f : X ⟶ Y, GW f → GW (realization.{u}.map f)

end DaggerActualQRealizationWeakEquivalencesChallenge
