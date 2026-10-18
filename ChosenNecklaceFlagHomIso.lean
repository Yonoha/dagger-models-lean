import ChosenNecklaceIntervalTerminal
import ChosenNecklaceIntervalPaths
import ChosenNecklaceOuterFlags
import ChosenFlagHomColimit

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b)

/-- The actual terminal interval leg is an isomorphism in the full flag colimit. -/
def intervalFlagLegIso : flagSSet.{u} (intervalCode T a b hab) ≅
    flagHom (toSSet.{u} T) (T.verticesEquiv.symm (ULift.up a))
      (T.verticesEquiv.symm (ULift.up b)) := by
  letI : IsIso (flagLeg _ _ _ (intervalOver T a b hab)) :=
    (flagIsColimit _ _ _).isIso_ι_app_of_isTerminal _ (intervalIsTerminal T a b hab)
  exact asIso (flagLeg _ _ _ (intervalOver T a b hab))

theorem intervalOrderMap_first :
    intervalOrderMap.{u} T a b hab (ULift.up 0) = ULift.up a :=
  ULift.ext _ _ (intervalEmbedding_first T a b hab)

theorem intervalOrderMap_last :
    intervalOrderMap.{u} T a b hab (ULift.up (Fin.last (b.val - a.val))) = ULift.up b :=
  ULift.ext _ _ (intervalEmbedding_last T a b hab)

/-- All unflanked cut flags identify with paths on the original target endpoints. -/
def intervalOuterHomIso : flagSSet.{u} (intervalCode T a b hab) ≅
    nerve (JointPath (T := T) (ULift.up a : Vertices.{u} T) (ULift.up b)) :=
  outerFlagIso (intervalCode T a b hab) ≪≫
    intervalHomIso T a b hab (ULift.up 0) (ULift.up (Fin.last (b.val - a.val))) ≪≫
      eqToIso (by
        rw [intervalOrderMap_first, intervalOrderMap_last])

/-- The full flag quotient on a necklace is its original joint-path Hom in every degree. -/
def necklaceFlagHomIso :
    flagHom (toSSet.{u} T) (T.verticesEquiv.symm (ULift.up a))
      (T.verticesEquiv.symm (ULift.up b)) ≅
        nerve (JointPath (T := T) (ULift.up a : Vertices.{u} T) (ULift.up b)) :=
  (intervalFlagLegIso T a b hab).symm ≪≫ intervalOuterHomIso T a b hab

theorem necklaceFlagHomIso_original_leg :
    flagLeg _ _ _ (intervalOver.{u} T a b hab) ≫ (necklaceFlagHomIso T a b hab).hom =
      (intervalOuterHomIso T a b hab).hom := by
  change (intervalFlagLegIso T a b hab).hom ≫
    ((intervalFlagLegIso T a b hab).inv ≫ (intervalOuterHomIso T a b hab).hom) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem necklaceFlagHomIso_inv : (necklaceFlagHomIso.{u} T a b hab).inv =
    (intervalOuterHomIso T a b hab).inv ≫ flagLeg _ _ _ (intervalOver T a b hab) := rfl

theorem necklaceFlagHomIso_operator {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌)
    (x : (flagHom (toSSet.{u} T) (T.verticesEquiv.symm (ULift.up a))
      (T.verticesEquiv.symm (ULift.up b))).obj (op ⦋n⦌)) :
    (necklaceFlagHomIso T a b hab).hom.app _
        ((flagHom _ _ _).map α.op x) =
      (nerve (JointPath (T := T) (ULift.up a : Vertices.{u} T) (ULift.up b))).map α.op
        ((necklaceFlagHomIso T a b hab).hom.app _ x) :=
  congrFun ((necklaceFlagHomIso T a b hab).hom.naturality α.op) x

end

end DaggerChosenRigidificationNecklace
