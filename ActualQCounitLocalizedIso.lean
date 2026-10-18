import ActualQDerivedAdjunction

/-! The literal original-Q counit is invertible after localization at every Kan target. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerNativeFibrantOppositeDerivability DaggerActualQDualFibrantDerived
open DaggerActualQDerivedEquivalence DaggerActualQDerivedAdjunction
open scoped SSet.modelCategoryQuillen
universe u v w

namespace DaggerActualQCounitLocalizedIso
noncomputable section

variable {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

local instance : (doubleLocalization L).IsLocalization doubleWeak.{u} :=
  doubleLocalization_isLocalization L

include L in
/-- The derived counit factorization detects the original transported counit on fibrant objects. -/
theorem doubleCounit_localized_isIso (X : (CofibrantObject SSet.{u}ᵒᵖ)ᵒᵖ) :
    IsIso (doubleWeak.Q.map (doubleAdjunction.counit.app
      ((dualFibrantInclusion SSet.{u}).functor.obj X))) := by
  have := DaggerActualQDerivedAdjunction.rightLeft_isRightDerivedFunctor L
  have : IsIso ((β L).app ((dualFibrantInclusion SSet.{u}).functor.obj X)) :=
    rightDerivedUnit_isIso L X
  have : IsIso (α L) := inferInstanceAs (IsIso (leftDerivedComparisonIso L).hom)
  have : IsIso (doubleAdjunction.derivedε doubleWeak (α L) (β L)) := by
    change IsIso (derivedAdjunction L).counit
    exact derivedCounit_isIso L
  have h : IsIso ((leftDerived L).map
      ((β L).app ((dualFibrantInclusion SSet.{u}).functor.obj X)) ≫
      (doubleAdjunction.derivedε doubleWeak (α L) (β L)).app
        (doubleWeak.Q.obj ((dualFibrantInclusion SSet.{u}).functor.obj X))) := inferInstance
  rw [doubleAdjunction.derivedε_fac_app doubleWeak (α L) (β L)] at h
  exact (isIso_comp_left_iff _ _).mp h

/-- Double opposition transports precisely the literal original counit map. -/
theorem doubleCounit_eq (X : SSet.{u}) :
    doubleAdjunction.counit.app (op (op X)) =
      (realizationSingularAdjunction.counit.app X).op.op := by
  simp [doubleAdjunction, Adjunction.comp_counit_app, doubleRealization, doubleSingular,
    opOpEquivalence, Equivalence.counit]

end
end DaggerActualQCounitLocalizedIso
