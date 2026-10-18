import ActualCoreOppositeMaps

/-! The original core/opposite comparison is natural and coherent over its inclusions. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeQuasicategoryOpposite DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerActualCoreOppositeMembership DaggerNativeSubcomplexOppositeRestriction
universe u
namespace DaggerActualOrdinaryCoreOpposite
noncomputable section

def coreOppositeIso (X : SSet.{u}) [X.Quasicategory] :
    (ordinaryCoreCandidate X : SSet.{u}).op ≅ (ordinaryCoreCandidate X.op : SSet.{u}) :=
  restrictionIso (ordinaryCoreCandidate X) (ordinaryCoreCandidate X.op)
    (op_mem_core X) (inv_mem_core X)

theorem core_hom_comp_inclusion (X : SSet.{u}) [X.Quasicategory] :
    (coreOppositeIso X).hom ≫ (ordinaryCoreCandidate X.op).ι =
      SSet.opFunctor.map (ordinaryCoreCandidate X).ι :=
  forward_comp_inclusion _ _ _

theorem core_inv_comp_inclusion (X : SSet.{u}) [X.Quasicategory] :
    (coreOppositeIso X).inv ≫ SSet.opFunctor.map (ordinaryCoreCandidate X).ι =
      (ordinaryCoreCandidate X.op).ι :=
  backward_comp_inclusion _ _ _

theorem coreOppositeIso_natural {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y) :
    SSet.opFunctor.map (ordinaryCoreCandidateMap f) ≫ (coreOppositeIso Y).hom =
      (coreOppositeIso X).hom ≫ ordinaryCoreCandidateMap (SSet.opFunctor.map f) := by
  apply (cancel_mono (ordinaryCoreCandidate Y.op).ι).mp
  calc
    _ = SSet.opFunctor.map (ordinaryCoreCandidateMap f) ≫
        SSet.opFunctor.map (ordinaryCoreCandidate Y).ι := by
      rw [Category.assoc, core_hom_comp_inclusion]
    _ = SSet.opFunctor.map (ordinaryCoreCandidateMap f ≫ (ordinaryCoreCandidate Y).ι) :=
      (CategoryTheory.Functor.map_comp _ _ _).symm
    _ = SSet.opFunctor.map ((ordinaryCoreCandidate X).ι ≫ f) := by
      rw [ordinaryCoreCandidateMap_comp_ι]
    _ = SSet.opFunctor.map (ordinaryCoreCandidate X).ι ≫ SSet.opFunctor.map f :=
      CategoryTheory.Functor.map_comp _ _ _
    _ = (coreOppositeIso X).hom ≫ (ordinaryCoreCandidate X.op).ι ≫
        SSet.opFunctor.map f := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ SSet.opFunctor.map f)
        (core_hom_comp_inclusion X).symm
    _ = _ := by simp only [Category.assoc, ordinaryCoreCandidateMap_comp_ι]

theorem coreOppositeIso_coherence (X : SSet.{u}) [X.Quasicategory] :
    SSet.opFunctor.map (coreOppositeIso X).hom ≫
      (@coreOppositeIso X.op (quasicategory_op X)).hom ≫
      ordinaryCoreCandidateMap (SSet.opFunctorCompOpFunctorIso.app X).hom =
        (SSet.opFunctorCompOpFunctorIso.app (ordinaryCoreCandidate X : SSet.{u})).hom := by
  apply (cancel_mono (ordinaryCoreCandidate X).ι).mp
  calc
    _ = SSet.opFunctor.map (coreOppositeIso X).hom ≫
        (@coreOppositeIso X.op (quasicategory_op X)).hom ≫
        (ordinaryCoreCandidate X.op.op).ι ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom := by
      rw [Category.assoc, Category.assoc, ordinaryCoreCandidateMap_comp_ι]
    _ = SSet.opFunctor.map (coreOppositeIso X).hom ≫
        SSet.opFunctor.map (ordinaryCoreCandidate X.op).ι ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ SSet.opFunctor.map (coreOppositeIso X).hom ≫ k ≫
          (SSet.opFunctorCompOpFunctorIso.app X).hom)
        (@core_hom_comp_inclusion X.op (quasicategory_op X))
    _ = SSet.opFunctor.map ((coreOppositeIso X).hom ≫ (ordinaryCoreCandidate X.op).ι) ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = SSet.opFunctor.map (SSet.opFunctor.map (ordinaryCoreCandidate X).ι) ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom := by rw [core_hom_comp_inclusion]
    _ = _ := SSet.opFunctorCompOpFunctorIso.hom.naturality (ordinaryCoreCandidate X).ι

end
end DaggerActualOrdinaryCoreOpposite
