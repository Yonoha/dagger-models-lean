import ActualRightConeTwoObjectCellIso
import OriginalCounitBNextConeEvaluationIndexReconciled

/-! The original adjunction classifies right-cone maps by two objects and one actual Q Hom map. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightCone DaggerOriginalEnrichedHomTransport
open DaggerActualRightConeTwoObjectCellIso
universe u

namespace DaggerActualRightConeMapClassification
noncomputable section

def mapEquiv (D : SimplicialCat.{u, u}) (n : ℕ) :
    (cone.{u} n ⟶ coherentNerve.{u}.obj D) ≃
      (Σ x : D.Obj, Σ y : D.Obj, Q.{u} n ⟶ (x ⟶[SSet.{u}] y)) :=
  (rigidificationCoherentNerveAdjunction.{u}.homEquiv (cone n) D).symm.trans
    ((Iso.homCongr (cellIso n).symm (Iso.refl D)).trans
      (OrdinaryTwoObjectCell.homEquiv (Q n) D))

/-- The forward Hom is unaltered by the cell comparison. -/
theorem mapEquiv_apply (D : SimplicialCat.{u, u}) (n : ℕ)
    (σ : cone.{u} n ⟶ coherentNerve.{u}.obj D) :
    mapEquiv D n σ =
      ⟨((rigidificationCoherentNerveAdjunction.homEquiv (cone n) D).symm σ).obj (alphaObj n),
        ((rigidificationCoherentNerveAdjunction.homEquiv (cone n) D).symm σ).obj (omegaObj n),
        ((rigidificationCoherentNerveAdjunction.homEquiv (cone n) D).symm σ).map
          (alphaObj n) (omegaObj n)⟩ := by
  change OrdinaryTwoObjectCell.classify
    ((cellIso n).hom ≫ (rigidificationCoherentNerveAdjunction.homEquiv (cone n) D).symm σ ≫
      𝟙 D) = _
  rw [Category.comp_id, cellIso_hom]
  let F := (rigidificationCoherentNerveAdjunction.homEquiv (cone n) D).symm σ
  change (⟨F.obj (alphaObj n), F.obj (omegaObj n),
    𝟙 (Q n) ≫ F.map (alphaObj n) (omegaObj n)⟩ :
      Σ x : D.Obj, Σ y : D.Obj, Q n ⟶ (x ⟶[SSet.{u}] y)) = _
  simp only [Category.id_comp, F]

theorem mapEquiv_first (D : SimplicialCat.{u, u}) (n : ℕ)
    (σ : cone.{u} n ⟶ coherentNerve.{u}.obj D) :
    (mapEquiv D n σ).1 = NerveVertices.vertexEquiv D (σ.app _ (alpha n)) := by
  rw [mapEquiv_apply]
  exact (functorObjEq (evaluation_functor D n σ) (alphaObj n)).symm.trans
    (evaluation_alpha_obj D n σ)

theorem mapEquiv_second (D : SimplicialCat.{u, u}) (n : ℕ)
    (σ : cone.{u} n ⟶ coherentNerve.{u}.obj D) :
    (mapEquiv D n σ).2.1 = NerveVertices.vertexEquiv D (σ.app _ (omega n)) := by
  rw [mapEquiv_apply]
  exact (functorObjEq (evaluation_functor D n σ) (omegaObj n)).symm.trans
    (evaluation_omega_obj D n σ)

end
end DaggerActualRightConeMapClassification
