import ActualOrdinaryCoreIsomorphismComparison
import ActualCoherentNerveIsomorphismCore
import ActualIsomorphismPartLocalWeakInvariance
import ActualRightConeRigidificationWeak
import NativeSimplicialCategoryIsoHom

/-! The SAME first core comparison is locally weak on nerves of locally Kan inputs.
The remaining arbitrary quasi-category case is not assumed or concluded here. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualSimplicialIsomorphismComponentPart
open DaggerActualOrdinaryCoreIsomorphismComparison
open DaggerOriginalOrdinaryKanCoreSubcomplex
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualCoherentNerveCoreComparisonWeak
noncomputable section

theorem nerve_quasi (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    (coherentNerve.obj C).Quasicategory :=
  DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory.coherentNerve_quasicategory C hC

def comparison (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    rigidification.obj (ordinaryCoreCandidate (coherentNerve.obj C) : SSet.{u}) ⟶
      part (rigidification.obj (coherentNerve.obj C)) :=
  @DaggerActualOrdinaryCoreIsomorphismComparison.comparison _ (nerve_quasi C hC)

theorem comparison_counit (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    comparison C hC ≫ DaggerActualSimplicialIsomorphismComponentMaps.map
        (rigidificationCoherentNerveAdjunction.counit.app C) =
      rigidification.map (DaggerActualCoherentNerveIsomorphismCore.comparisonIso C hC).inv ≫
        rigidificationCoherentNerveAdjunction.counit.app (part C) := by
  have := nerve_quasi C hC
  have := DaggerActualOrdinaryCoreIsomorphismComparison.inclusion_mono C
  apply (cancel_mono (inclusion C)).mp
  have hl : (comparison C hC ≫ DaggerActualSimplicialIsomorphismComponentMaps.map
      (rigidificationCoherentNerveAdjunction.counit.app C)) ≫ inclusion C =
      rigidification.map (ordinaryCoreCandidate (coherentNerve.obj C)).ι ≫
        rigidificationCoherentNerveAdjunction.counit.app C := by
    rw [Category.assoc, DaggerActualSimplicialIsomorphismComponentMaps.inclusion_natural,
      ← Category.assoc]
    exact congrArg (fun F ↦ F ≫ rigidificationCoherentNerveAdjunction.counit.app C)
      (comparison_comp_inclusion (coherentNerve.obj C))
  have hn := rigidificationCoherentNerveAdjunction.counit.naturality (inclusion C)
  change rigidification.map (coherentNerve.map (inclusion C)) ≫
      rigidificationCoherentNerveAdjunction.counit.app C =
    rigidificationCoherentNerveAdjunction.counit.app (part C) ≫ inclusion C at hn
  rw [hl, Category.assoc, ← hn, ← Category.assoc, ← rigidification.map_comp,
    DaggerActualCoherentNerveIsomorphismCore.inv_comp_inclusion]

theorem counit_part_hom_weak (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (a b : (part (rigidification.obj (coherentNerve.obj C))).Obj) :
    WeakEquivalence ((DaggerActualSimplicialIsomorphismComponentMaps.map
      (rigidificationCoherentNerveAdjunction.counit.app C)).map a b) :=
  DaggerActualIsomorphismPartLocalWeakInvariance.hom_weak _
    (fun x y ↦ (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (DaggerActualRightConeRigidificationWeak.ordinary_counit_local C hC x y)) a b

theorem hom_weak (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (a b : (rigidification.obj
      (ordinaryCoreCandidate (coherentNerve.obj C) : SSet.{u})).Obj) :
    WeakEquivalence ((comparison C hC).map a b) := by
  let e := DaggerActualCoherentNerveIsomorphismCore.comparisonIso C hC
  let F := rigidification.map e.inv
  let E := rigidificationCoherentNerveAdjunction.counit.app (part C)
  let P := DaggerActualSimplicialIsomorphismComponentMaps.map
    (rigidificationCoherentNerveAdjunction.counit.app C)
  have : IsIso (F.map a b) :=
    DaggerNativeSimplicialCategoryIsoHom.hom_isIso (rigidification.mapIso e.symm) a b
  have : WeakEquivalence (E.map (F.obj a) (F.obj b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (DaggerActualRightConeRigidificationWeak.ordinary_counit_local (part C)
        (DaggerActualIsomorphismPartFibrancy.locallyKan C hC) (F.obj a) (F.obj b))
  have hw : WeakEquivalence ((F ≫ E).map a b) := by
    change WeakEquivalence (F.map a b ≫ E.map (F.obj a) (F.obj b))
    infer_instance
  have hc : WeakEquivalence (((comparison C hC) ≫ P).map a b) := by
    change WeakEquivalence ((comparison C hC ≫
      DaggerActualSimplicialIsomorphismComponentMaps.map
        (rigidificationCoherentNerveAdjunction.counit.app C)).map a b)
    rw [comparison_counit]
    exact hw
  have : WeakEquivalence (P.map ((comparison C hC).obj a) ((comparison C hC).obj b)) :=
    counit_part_hom_weak C hC _ _
  have : WeakEquivalence ((comparison C hC).map a b ≫
      P.map ((comparison C hC).obj a) ((comparison C hC).obj b)) := hc
  exact weakEquivalence_of_postcomp ((comparison C hC).map a b)
    (P.map ((comparison C hC).obj a) ((comparison C hC).obj b))

end
end DaggerActualCoherentNerveCoreComparisonWeak
