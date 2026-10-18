import ActualQCounitLocalizedIso

/-! Every localization at native Kan weak equivalences inverts the literal original-Q counit. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerNativeFibrantOppositeDerivability DaggerActualQDualFibrantDerived
open DaggerActualQDerivedEquivalence DaggerActualQDerivedAdjunction
open DaggerActualQCounitLocalizedIso
open scoped SSet.modelCategoryQuillen
universe u v w

namespace DaggerActualQOriginalCounitLocalization
noncomputable section

/-- The canonical localization inverts exactly the transported original counit on Kan objects. -/
theorem canonical_double_counit_isIso (X : SSet.{u}) [X.KanComplex] :
    IsIso (doubleWeak.Q.map (realizationSingularAdjunction.counit.app X).op.op) := by
  have : IsCofibrant (op X) := (isCofibrant_op_iff_isFibrant X).mpr inferInstance
  have h := doubleCounit_localized_isIso (weakEquivalences SSet.{u}).Q
    (op (CofibrantObject.mk (op X)))
  change IsIso (doubleWeak.Q.map (doubleAdjunction.counit.app (op (op X)))) at h
  rwa [doubleCounit_eq] at h

variable {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

/-- The conclusion concerns the unchanged original counit, for any actual localization. -/
theorem counit_localized_isIso (X : SSet.{u}) [X.KanComplex] :
    IsIso (L.map (realizationSingularAdjunction.counit.app X)) := by
  have := doubleLocalization_isLocalization L
  have := canonical_double_counit_isIso X
  let E := Localization.uniq doubleWeak.Q (doubleLocalization L) doubleWeak
  let e := Localization.compUniqFunctor doubleWeak.Q (doubleLocalization L) doubleWeak
  let f := (realizationSingularAdjunction.counit.app X).op.op
  have : IsIso (E.functor.map (doubleWeak.Q.map f)) := inferInstance
  have h : IsIso (e.hom.app _ ≫
      (doubleLocalization L).map f) := by
    rw [← e.hom.naturality f]
    change IsIso (E.functor.map (doubleWeak.Q.map f) ≫ e.hom.app _)
    infer_instance
  exact (isIso_comp_left_iff _ _).mp h

end
end DaggerActualQOriginalCounitLocalization
