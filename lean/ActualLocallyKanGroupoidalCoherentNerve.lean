import NativeQuasicategoryGroupoidKan
import ActualIsomorphismPartComponents
import ActualRightConeRigidificationWeak
import ActualRigidificationComponentHoComparison
import OriginalPiZeroGroupoidLocalWeakInvariance
import OriginalOrdinaryNerveQuasicategory

/-! The ORIGINAL coherent nerve of every locally Kan category with groupoidal pi-zero is Kan. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalPiZeroGroupoidLocalWeakInvariance DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualLocallyKanGroupoidalCoherentNerve
noncomputable section

theorem rigidification_component_groupoid (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hG : HasActualComponentGroupoid C) :
    HasActualComponentGroupoid (rigidification.obj (coherentNerve.obj C)) := by
  apply reflected (rigidificationCoherentNerveAdjunction.counit.app C) _ hG
  intro a b
  exact (weakEquivalence_iff_GW _).2
    (DaggerActualRightConeRigidificationWeak.ordinary_counit_local C hC a b)

theorem ho_isIso (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hG : HasActualComponentGroupoid C)
    {x y : SSet.hoFunctor.obj (coherentNerve.obj C)} (f : x ⟶ y) : IsIso f := by
  let E := DaggerActualRigidificationComponentHoComparison.componentHoEquivalence
    (coherentNerve.obj C)
  have : IsIso (E.inverse.map f) :=
    component_isIso _ (rigidification_component_groupoid C hC hG) _
  exact isIso_of_reflects_iso f E.inverse

theorem kan (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hG : HasActualComponentGroupoid C) : (coherentNerve.obj C).KanComplex := by
  have := DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory.coherentNerve_quasicategory
    C hC
  exact DaggerNativeQuasicategoryGroupoidKan.kan _ (ho_isIso C hC hG)

theorem part_kan (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    (coherentNerve.obj (DaggerActualSimplicialIsomorphismComponentPart.part C)).KanComplex :=
  kan _ (DaggerActualIsomorphismPartFibrancy.locallyKan C hC)
    (DaggerActualIsomorphismPartComponents.component_groupoid C hC)

theorem replacement_part_kan (C : SimplicialCat.{u, u}) :
    (coherentNerve.obj (DaggerActualSimplicialIsomorphismComponentPart.part
      (OriginalOrdinaryLocalKanReplacement.replacement.obj C))).KanComplex :=
  part_kan _ (OriginalOrdinaryLocalKanReplacement.replacement_locallyKan C)

end
end DaggerActualLocallyKanGroupoidalCoherentNerve
