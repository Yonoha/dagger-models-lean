import ChosenNecklaceFlagEvaluationIso

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode) {x y : (toSSet.{u} T).obj (op ⦋0⦌)}

include x y in
theorem reverseFlagElim (hn : ¬(T.verticesEquiv x).down ≤ (T.verticesEquiv y).down)
    (q : SimplexCategoryᵒᵖ) (v : (flagHom (toSSet.{u} T) x y).obj q) : False := by
  induction v using Quot.ind with | _ p
  exact hn (over_endpoints_le T _ _ (overAtCoordinates p.1))

/-- Reverse endpoint Homs are genuinely empty on both sides, not a chosen replacement Hom. -/
def reverseFlagEvaluationIso
    (hn : ¬(T.verticesEquiv x).down ≤ (T.verticesEquiv y).down) :
    flagHom (toSSet.{u} T) x y ≅ nerve (JointPath (T.verticesEquiv x) (T.verticesEquiv y)) where
  hom := necklaceFlagEvaluation T
  inv :=
    { app q F := (hn (F.obj 0).le).elim
      naturality p q α := by
        funext F
        exact (hn (F.obj 0).le).elim }
  hom_inv_id := by
    apply NatTrans.ext
    funext q v
    exact (reverseFlagElim T hn q v).elim
  inv_hom_id := by
    apply NatTrans.ext
    funext q F
    exact (hn (F.obj 0).le).elim

/-- Every original Hom, including diagonal and reversed pairs, has the full evaluation iso. -/
instance necklaceFlagEvaluation_all_isIso (x y : (toSSet.{u} T).obj (op ⦋0⦌)) :
    IsIso (necklaceFlagEvaluation (x := x) (y := y) T) := by
  by_cases hab : (T.verticesEquiv x).down ≤ (T.verticesEquiv y).down
  · have h := necklaceFlagEvaluation_isIso.{u} T _ _ hab
    have hx : ULift.up (T.verticesEquiv x).down = T.verticesEquiv x := by
      cases T.verticesEquiv x
      rfl
    have hy : ULift.up (T.verticesEquiv y).down = T.verticesEquiv y := by
      cases T.verticesEquiv y
      rfl
    have hxx : T.verticesEquiv.symm (ULift.up (T.verticesEquiv x).down) = x :=
      (congrArg T.verticesEquiv.symm hx).trans (T.verticesEquiv.symm_apply_apply x)
    have hyy : T.verticesEquiv.symm (ULift.up (T.verticesEquiv y).down) = y :=
      (congrArg T.verticesEquiv.symm hy).trans (T.verticesEquiv.symm_apply_apply y)
    rw [hxx, hyy] at h
    exact h
  · exact (reverseFlagEvaluationIso T hab).isIso_hom

/-- Full original Hom iso, with hom literally the image-of-vertices evaluation. -/
def necklaceEvaluationIso (x y : (toSSet.{u} T).obj (op ⦋0⦌)) :
    flagHom (toSSet.{u} T) x y ≅ nerve (JointPath (T.verticesEquiv x) (T.verticesEquiv y)) :=
  asIso (necklaceFlagEvaluation T)

theorem necklaceEvaluationIso_hom (x y : (toSSet.{u} T).obj (op ⦋0⦌)) :
    (necklaceEvaluationIso T x y).hom = necklaceFlagEvaluation T := rfl

end

end DaggerChosenRigidificationNecklace
