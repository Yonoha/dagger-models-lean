import ChosenNecklaceAllHomIsos

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode) (a b : NecklaceThickening.{u} T)

def inverseHomEndpointEq :
    nerve (JointPath (T.verticesEquiv (T.verticesEquiv.symm a.as))
      (T.verticesEquiv (T.verticesEquiv.symm b.as))) = pathHom a b := by
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The Hom iso at the specified original NC objects, with both inverse-object casts. -/
def necklaceInverseHomIso :
    flagHom (toSSet.{u} T) (T.verticesEquiv.symm a.as) (T.verticesEquiv.symm b.as) ≅
      pathHom a b :=
  necklaceEvaluationIso T _ _ ≪≫ eqToIso (inverseHomEndpointEq T a b)

theorem necklaceInverseHomIso_I (q : SimplexCategoryᵒᵖ)
    (v : (flagHom (toSSet.{u} T) (T.verticesEquiv.symm a.as)
      (T.verticesEquiv.symm b.as)).obj q) (i : Fin (q.unop.len + 1)) :
    ((((necklaceInverseHomIso T a b).hom.app q v).obj i).I) =
      (((necklaceFlagEvaluation T).app q v).obj i).I := by
  change (((eqToHom (inverseHomEndpointEq T a b) :
    nerve (JointPath (T.verticesEquiv (T.verticesEquiv.symm a.as))
      (T.verticesEquiv (T.verticesEquiv.symm b.as))) ⟶ pathHom a b).app q
        ((necklaceFlagEvaluation T).app q v)).obj i).I = _
  exact pathHom_eqToHom_I
    (congrArg NecklaceThickening.mk (T.verticesEquiv.apply_symm_apply a.as))
    (congrArg NecklaceThickening.mk (T.verticesEquiv.apply_symm_apply b.as)) _ _ _ _

theorem necklaceInverseHomIso_identity (a : NecklaceThickening.{u} T) :
    flagIdentity (toSSet T) (T.verticesEquiv.symm a.as) ≫
      (necklaceInverseHomIso T a a).hom = pathId a := by
  apply NatTrans.ext
  funext q v
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change ((((necklaceInverseHomIso T a a).hom.app q
      (flagIdApp (T.verticesEquiv.symm a.as) q)).obj i).I) = {a.as}
    rw [necklaceInverseHomIso_I]
    have h := congrArg (fun F ↦ (F.obj i).I)
      (congrFun (NatTrans.congr_app
        (necklaceFlagEvaluation_identity T (T.verticesEquiv.symm a.as)) q) v)
    change (((necklaceFlagEvaluation T).app q
      (flagIdApp (T.verticesEquiv.symm a.as) q)).obj i).I =
        {T.verticesEquiv (T.verticesEquiv.symm a.as)} at h
    simpa only [Equiv.apply_symm_apply] using h))

theorem necklaceInverseHomIso_composition (a b c : NecklaceThickening.{u} T) :
    flagComposition (toSSet T) (T.verticesEquiv.symm a.as) (T.verticesEquiv.symm b.as)
      (T.verticesEquiv.symm c.as) ≫ (necklaceInverseHomIso T a c).hom =
    ((necklaceInverseHomIso T a b).hom ⊗ₘ (necklaceInverseHomIso T b c).hom) ≫
      pathComp a b c := by
  apply NatTrans.ext
  funext q v
  rcases v with ⟨v,w⟩
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change ((((necklaceInverseHomIso T a c).hom.app q
        (flagCompApp v w)).obj i).I) =
      ((((necklaceInverseHomIso T a b).hom.app q v).obj i).I) ∪
        ((((necklaceInverseHomIso T b c).hom.app q w).obj i).I)
    rw [necklaceInverseHomIso_I, necklaceInverseHomIso_I, necklaceInverseHomIso_I]
    exact congrArg (fun F ↦ (F.obj i).I)
      (congrFun (NatTrans.congr_app (necklaceFlagEvaluation_composition T _ _ _) q) (v,w))))

end

end DaggerChosenRigidificationNecklace
