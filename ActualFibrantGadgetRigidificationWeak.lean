import ActualFibrantGadgetData
import ActualFibrantGadgetVertices
import ActualRightConeRigidificationWeak
import OriginalLocalKanReplacementDiagonalWeak

/-! The ORIGINAL gadget unit has weak rigidified Homs, on EVERY original simplicial set. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite Simplicial DaggerModels OrdinaryRigidification
open OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualFibrantGadgetRigidificationWeak
noncomputable section

theorem triangle (X : SSet.{u}) :
    rigidification.map (DaggerActualFibrantGadgetData.unit.app X) ≫
      rigidificationCoherentNerveAdjunction.counit.app
        (replacement.obj (rigidification.obj X)) =
      unit.app (rigidification.obj X) := by
  change rigidification.map (rigidificationCoherentNerveAdjunction.homEquiv X
    (replacement.obj (rigidification.obj X)) (unit.app (rigidification.obj X))) ≫ _ = _
  exact (rigidificationCoherentNerveAdjunction.homEquiv_counit
    (g := rigidificationCoherentNerveAdjunction.homEquiv X
      (replacement.obj (rigidification.obj X)) (unit.app (rigidification.obj X)))).symm.trans
        ((rigidificationCoherentNerveAdjunction.homEquiv X
          (replacement.obj (rigidification.obj X))).symm_apply_apply _)

theorem hom_weak (X : SSet.{u}) (a b : (rigidification.obj X).Obj) :
    WeakEquivalence ((rigidification.map (DaggerActualFibrantGadgetData.unit.app X)).map a b) := by
  let F := rigidification.map (DaggerActualFibrantGadgetData.unit.app X)
  let E := rigidificationCoherentNerveAdjunction.counit.app
    (replacement.obj (rigidification.obj X))
  have : WeakEquivalence (E.map (F.obj a) (F.obj b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (DaggerActualRightConeRigidificationWeak.ordinary_counit_local _
        (replacement_locallyKan _) (F.obj a) (F.obj b))
  have hw : WeakEquivalence ((F ≫ E).map a b) := by
    change WeakEquivalence
      ((rigidification.map (DaggerActualFibrantGadgetData.unit.app X) ≫ E).map a b)
    rw [show rigidification.map (DaggerActualFibrantGadgetData.unit.app X) ≫ E =
      unit.app (rigidification.obj X) from triangle X]
    exact DaggerOriginalLocalKanReplacementDiagonalWeak.unit_hom_weak _ a b
  have : WeakEquivalence (F.map a b ≫ E.map (F.obj a) (F.obj b)) := hw
  exact weakEquivalence_of_postcomp (F.map a b) (E.map (F.obj a) (F.obj b))

theorem object_bijective (X : SSet.{u}) :
    Function.Bijective (rigidification.map (DaggerActualFibrantGadgetData.unit.app X)).obj := by
  have h := DaggerActualFibrantGadgetVertices.unit_vertex_bijective X
  let eX := RigidificationVertices.vertexEquiv X
  let eY := RigidificationVertices.vertexEquiv (DaggerActualFibrantGadgetData.gadget.obj X)
  have he : (rigidification.map (DaggerActualFibrantGadgetData.unit.app X)).obj =
      eY ∘ (DaggerActualFibrantGadgetData.unit.app X).app (Opposite.op ⦋0⦌) ∘ eX.symm := by
    funext a
    simpa only [eX, eY, Function.comp_apply, Functor.id_obj, Equiv.apply_symm_apply] using
      RigidificationVertices.vertexEquiv_naturality
        (DaggerActualFibrantGadgetData.unit.app X) (eX.symm a)
  rw [he]
  exact eY.bijective.comp (h.comp eX.symm.bijective)

end
end DaggerActualFibrantGadgetRigidificationWeak
