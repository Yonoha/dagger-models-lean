import ActualRightConeMapClassification

/-! Fixed-endpoint right-cone maps are exactly maps from the literal Q Hom. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightCone DaggerOriginalEnrichedHomTransport
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerActualRightConeMapClassification
open DaggerChosenRigidificationNecklace hiding C RV
universe u

namespace DaggerActualRightConeFixedMapEquivalence
noncomputable section

private theorem data_transport_congr (K : SSet.{u}) (D : SimplicialCat.{u, u})
    {d e : Σ a : D.Obj, Σ b : D.Obj, K ⟶ (a ⟶[SSet.{u}] b)} (h : d = e)
    (x y : D.Obj) (hd0 : d.1 = x) (hd1 : d.2.1 = y)
    (he0 : e.1 = x) (he1 : e.2.1 = y) :
    d.2.2 ≫ targetHomTransport hd0 hd1 = e.2.2 ≫ targetHomTransport he0 he1 := by
  cases h
  rfl

def fixedDataEquiv (K : SSet.{u}) (D : SimplicialCat.{u, u}) (x y : D.Obj) :
    {d : (Σ a : D.Obj, Σ b : D.Obj, K ⟶ (a ⟶[SSet.{u}] b)) //
      d.1 = x ∧ d.2.1 = y} ≃ (K ⟶ (x ⟶[SSet.{u}] y)) where
  toFun d := d.1.2.2 ≫ targetHomTransport d.2.1 d.2.2
  invFun f := ⟨⟨x, y, f⟩, rfl, rfl⟩
  left_inv := by
    rintro ⟨⟨a, b, f⟩, ha, hb⟩
    cases ha
    cases hb
    apply Subtype.ext
    simp only [targetHomTransport, eqToHom_refl, Category.comp_id]
  right_inv f := by
    simp only [targetHomTransport, eqToHom_refl, Category.comp_id]

def fixedMapEquiv (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) (n : ℕ) :
    (rightConeSimplices.{u} D v w).obj (op ⦋n⦌) ≃
      (Q.{u} n ⟶ (NerveVertices.vertexEquiv D v ⟶[SSet.{u}]
        NerveVertices.vertexEquiv D w)) :=
  (Equiv.subtypeEquiv (mapEquiv D n) (by
    intro σ
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨(mapEquiv_first D n σ).trans (congrArg (NerveVertices.vertexEquiv D) ha),
        (mapEquiv_second D n σ).trans (congrArg (NerveVertices.vertexEquiv D) hb)⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(NerveVertices.vertexEquiv D).injective ((mapEquiv_first D n σ).symm.trans ha),
        (NerveVertices.vertexEquiv D).injective
          ((mapEquiv_second D n σ).symm.trans hb)⟩)).trans
    (fixedDataEquiv (Q n) D (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w))

/-- This equivalence uses precisely the original adjunction counit evaluation and both casts. -/
theorem fixedMapEquiv_apply (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices.{u} D v w).obj (op ⦋n⦌)) :
    fixedMapEquiv D v w n σ = rightConeEvaluation D v w n σ := by
  let F := (rigidificationCoherentNerveAdjunction.homEquiv (cone n) D).symm σ.1
  have h0 : F.obj (alphaObj n) = NerveVertices.vertexEquiv D v :=
    ((functorObjEq (evaluation_functor D n σ.1) (alphaObj n)).symm.trans
      (evaluation_alpha_obj D n σ.1)).trans (congrArg (NerveVertices.vertexEquiv D) σ.2.1)
  have h1 : F.obj (omegaObj n) = NerveVertices.vertexEquiv D w :=
    ((functorObjEq (evaluation_functor D n σ.1) (omegaObj n)).symm.trans
      (evaluation_omega_obj D n σ.1)).trans (congrArg (NerveVertices.vertexEquiv D) σ.2.2)
  have he : fixedMapEquiv D v w n σ =
      F.map (alphaObj n) (omegaObj n) ≫ targetHomTransport h0 h1 := by
    change (mapEquiv D n σ.1).2.2 ≫ targetHomTransport _ _ = _
    exact data_transport_congr (Q n) D (mapEquiv_apply D n σ.1)
      (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w) _ _ h0 h1
  rw [he]
  have hc := enrichedFunctor_hom_congr_to_fixed (evaluation_functor D n σ.1).symm
    (alphaObj n) (omegaObj n) (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w)
    h0 h1
    ((evaluation_alpha_obj D n σ.1).trans (congrArg (NerveVertices.vertexEquiv D) σ.2.1))
    ((evaluation_omega_obj D n σ.1).trans (congrArg (NerveVertices.vertexEquiv D) σ.2.2))
  refine hc.trans ?_
  unfold rightConeEvaluation DaggerOriginalCounitRightCone.evaluation
  rw [Category.assoc, Category.assoc, targetHomTransport_trans]
  rfl

theorem evaluation_bijective (D : SimplicialCat.{u, u})
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) (n : ℕ) :
    Function.Bijective (rightConeEvaluation.{u} D v w n) := by
  have h : rightConeEvaluation D v w n = fixedMapEquiv D v w n :=
    funext (fun σ ↦ (fixedMapEquiv_apply D v w n σ).symm)
  rw [h]
  exact (fixedMapEquiv D v w n).bijective

end
end DaggerActualRightConeFixedMapEquivalence
