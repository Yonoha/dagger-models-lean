import ActualSimplicialIsomorphismComponentFactor
import ActualKanRigidificationCompletionWeak
import NativeEnrichedHomRestrictionMonomorphism

/-! ALL Kan-source maps into the original coherent nerve factor through the ALL-isomorphism part. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualSimplicialIsomorphismComponentPart
universe u
namespace DaggerNativeCoherentNerveIsomorphismPartKanFactor
noncomputable section

theorem inclusion_mono (C : SimplicialCat.{u, u}) : Mono (coherentNerve.map (inclusion C)) where
  right_cancellation := by
    intro K f g h
    have : Mono (inclusion C) :=
      DaggerNativeEnrichedHomRestrictionMonomorphism.inclusion_mono C
        (homSubcomplex C) (id_mem C) (comp_mem C)
    let fa : rigidification.obj K ⟶ part C :=
      (rigidificationCoherentNerveAdjunction.homEquiv K (part C)).symm f
    let ga : rigidification.obj K ⟶ part C :=
      (rigidificationCoherentNerveAdjunction.homEquiv K (part C)).symm g
    have ha : fa ≫ inclusion C = ga ≫ inclusion C := by
      apply (rigidificationCoherentNerveAdjunction.homEquiv K C).injective
      simpa only [rigidificationCoherentNerveAdjunction.homEquiv_naturality_right,
        fa, ga, Equiv.apply_symm_apply] using h
    exact (rigidificationCoherentNerveAdjunction.homEquiv K (part C)).symm.injective
      ((cancel_mono (inclusion C)).mp ha)

def factor {K : SSet.{u}} [K.KanComplex] (C : SimplicialCat.{u, u})
    (f : K ⟶ coherentNerve.obj C) : K ⟶ coherentNerve.obj (part C) :=
  rigidificationCoherentNerveAdjunction.homEquiv K (part C)
    (DaggerActualSimplicialIsomorphismComponentFactor.factor
      ((rigidificationCoherentNerveAdjunction.homEquiv K C).symm f)
      (DaggerActualKanRigidificationCompletionWeak.component_groupoid K))

theorem factor_comp_inclusion {K : SSet.{u}} [K.KanComplex] (C : SimplicialCat.{u, u})
    (f : K ⟶ coherentNerve.obj C) : factor C f ≫ coherentNerve.map (inclusion C) = f := by
  unfold factor
  rw [← rigidificationCoherentNerveAdjunction.homEquiv_naturality_right,
    DaggerActualSimplicialIsomorphismComponentFactor.factor_comp_inclusion,
    Equiv.apply_symm_apply]

theorem factor_unique {K : SSet.{u}} [K.KanComplex] (C : SimplicialCat.{u, u})
    (f : K ⟶ coherentNerve.obj C) (g : K ⟶ coherentNerve.obj (part C))
    (h : g ≫ coherentNerve.map (inclusion C) = f) : g = factor C f := by
  have := inclusion_mono C
  apply (cancel_mono (coherentNerve.map (inclusion C))).mp
  rw [h, factor_comp_inclusion]

end
end DaggerNativeCoherentNerveIsomorphismPartKanFactor
