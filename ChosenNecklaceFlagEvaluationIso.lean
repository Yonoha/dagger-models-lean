import ChosenNecklaceFlagHomIso
import ChosenNecklaceFlagEnrichedEvaluation

open CategoryTheory EnrichedCategory MonoidalCategory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b)

def intervalPathEndpointEq :
    nerve (JointPath (intervalOrderMap.{u} T a b hab (ULift.up 0))
      (intervalOrderMap T a b hab (ULift.up (Fin.last (b.val - a.val))))) =
        nerve (JointPath (T := T) (ULift.up a : Vertices.{u} T) (ULift.up b)) := by
  rw [intervalOrderMap_first, intervalOrderMap_last]

def evaluationEndpointEq :
    nerve (JointPath (T.verticesEquiv.symm (ULift.up a) |> T.verticesEquiv)
      (T.verticesEquiv.symm (ULift.up b) |> T.verticesEquiv)) =
        nerve (JointPath (T := T) (ULift.up a : Vertices.{u} T) (ULift.up b)) := by
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem intervalOuterHomIso_I {n : ℕ}
    (F : NecklaceCode.Flag.{u} (intervalCode T a b hab) n) (i : Fin (n + 1)) :
    ((((intervalOuterHomIso T a b hab).hom.app (op ⦋n⦌) F).obj i).I) =
      intervalOrderMap T a b hab '' F.chain i := by
  change (((eqToHom (intervalPathEndpointEq T a b hab) :
    nerve (JointPath (intervalOrderMap T a b hab (ULift.up 0))
      (intervalOrderMap T a b hab (ULift.up (Fin.last (b.val - a.val))))) ⟶
        nerve (JointPath (T := T) (ULift.up a : Vertices.{u} T) (ULift.up b))).app (op ⦋n⦌)
    ((intervalHomIso T a b hab (ULift.up 0) (ULift.up (Fin.last (b.val - a.val)))).hom.app (op ⦋n⦌)
      ((outerFlagIso (intervalCode T a b hab)).hom.app (op ⦋n⦌) F))).obj i).I = _
  rw [pathHom_eqToHom_I (T := T)
    (congrArg NecklaceThickening.mk (intervalOrderMap_first T a b hab))
    (congrArg NecklaceThickening.mk (intervalOrderMap_last T a b hab))]
  rfl

theorem necklaceFlagEvaluation_interval_leg :
    flagLeg _ _ _ (intervalOver.{u} T a b hab) ≫ necklaceFlagEvaluation.{u} T ≫
        eqToHom (evaluationEndpointEq T a b) =
      (intervalOuterHomIso T a b hab).hom := by
  apply NatTrans.ext
  funext q F
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change (((eqToHom (evaluationEndpointEq T a b) :
      nerve (JointPath (T.verticesEquiv (T.verticesEquiv.symm (ULift.up a)))
        (T.verticesEquiv (T.verticesEquiv.symm (ULift.up b)))) ⟶
      nerve (JointPath (T := T) (ULift.up a : Vertices.{u} T) (ULift.up b))).app (op ⦋n⦌)
      (overFlagNerve T (intervalOver T a b hab) F)).obj i).I = _
    rw [pathHom_eqToHom_I (T := T)
      (congrArg NecklaceThickening.mk (T.verticesEquiv.apply_symm_apply (ULift.up a)))
      (congrArg NecklaceThickening.mk (T.verticesEquiv.apply_symm_apply (ULift.up b))),
      intervalOuterHomIso_I (n := n) T a b hab F i]
    change mapVertices (intervalι T a b hab) '' F.chain i =
      intervalOrderMap T a b hab '' F.chain i
    congr 1
    funext v
    exact intervalι_vertices T a b hab v))

/-- Full original evaluation is an isomorphism; no fibrancy or distinctness is involved. -/
instance necklaceFlagEvaluation_isIso :
    IsIso (necklaceFlagEvaluation.{u} (x := T.verticesEquiv.symm (ULift.up a))
      (y := T.verticesEquiv.symm (ULift.up b)) T) := by
  letI : IsIso (flagLeg _ _ _ (intervalOver.{u} T a b hab)) :=
    (flagIsColimit _ _ _).isIso_ι_app_of_isTerminal _ (intervalIsTerminal T a b hab)
  have he := necklaceFlagEvaluation_interval_leg T a b hab
  haveI : IsIso
      (flagLeg _ _ _ (intervalOver.{u} T a b hab) ≫ necklaceFlagEvaluation.{u} T ≫
        eqToHom (evaluationEndpointEq T a b)) := by
    rw [he]
    infer_instance
  haveI : IsIso ((flagLeg _ _ _ (intervalOver T a b hab) ≫ necklaceFlagEvaluation.{u} T) ≫
      eqToHom (evaluationEndpointEq T a b)) := by
    rw [Category.assoc]
    infer_instance
  haveI : IsIso (flagLeg _ _ _ (intervalOver T a b hab) ≫ necklaceFlagEvaluation.{u} T) :=
    IsIso.of_isIso_comp_right _ (eqToHom (evaluationEndpointEq T a b))
  exact IsIso.of_isIso_comp_left (flagLeg _ _ _ (intervalOver T a b hab))
    (necklaceFlagEvaluation.{u} T)

end

end DaggerChosenRigidificationNecklace
