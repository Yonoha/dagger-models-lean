import OriginalSingularSetReversal
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Geometric realization commutes with actual simplicial reversal

The comparison follows from the existing realization/singular adjunction,
the involutive equivalence of simplicial sets, and the actual singular-set
reversal isomorphism. It does not assert coordinate-level or involution
coherence for a dagger on a realized space.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace DaggerOriginalRealizationOppositeComparison

noncomputable section

/-- Reversal followed by actual realization is left adjoint to the reversed
singular simplicial set. -/
def oppositeRealizationAdjunction :
    SSet.opFunctor.{u} ⋙ SSet.toTop.{u} ⊣
      TopCat.toSSet.{u} ⋙ SSet.opFunctor.{u} :=
  SSet.opEquivalence.{u}.toAdjunction.comp sSetTopAdj.{u}

/-- The existing singular reversal identifies the right adjoint with the
ordinary singular-set functor. -/
def oppositeRealizationAdjunctionToSing :
    SSet.opFunctor.{u} ⋙ SSet.toTop.{u} ⊣ TopCat.toSSet.{u} :=
  oppositeRealizationAdjunction.ofNatIsoRight
    DaggerOriginalSingularSetReversal.singularReversal.{u}

/-- The actual realization of a reversed simplicial set agrees naturally
with the actual realization of the original simplicial set. -/
def realizationOppositeIso :
    SSet.opFunctor.{u} ⋙ SSet.toTop.{u} ≅ SSet.toTop.{u} :=
  Adjunction.leftAdjointUniq oppositeRealizationAdjunctionToSing sSetTopAdj

/-- The comparison respects the two units into the same singular functor. -/
theorem realizationOppositeIso_unit (X : SSet.{u}) :
    oppositeRealizationAdjunctionToSing.unit.app X ≫
      TopCat.toSSet.{u}.map (realizationOppositeIso.hom.app X) =
        sSetTopAdj.unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app
    oppositeRealizationAdjunctionToSing sSetTopAdj X

end

end DaggerOriginalRealizationOppositeComparison
