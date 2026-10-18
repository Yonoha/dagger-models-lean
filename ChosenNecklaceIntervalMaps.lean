import ChosenNecklaceIntervalCode
import ChosenNecklacePointMaps

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b)

def intervalι : toSSet.{u} (intervalCode T a b hab) ⟶ toSSet.{u} T :=
  orderLift (intervalEmbedding T a b hab).toOrderHom (interval_image T a b hab)

theorem intervalι_vertices (v : Vertices.{u} (intervalCode T a b hab)) :
    mapVertices (intervalι T a b hab) v = ULift.up (intervalEmbedding T a b hab v.down) :=
  orderLift_vertices _ _ v

theorem intervalι_inclusion :
    intervalι.{u} T a b hab ≫ T.inclusion =
      (intervalCode T a b hab).inclusion ≫ SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (intervalEmbedding T a b hab).toOrderHom :
          ⦋(intervalCode T a b hab).len⦌ ⟶ ⦋T.len⦌) :=
  orderLift_inclusion _ _

theorem intervalι_first :
    (intervalι.{u} T a b hab).app _ (intervalCode T a b hab).first =
      T.verticesEquiv.symm (ULift.up a) := by
  apply T.verticesEquiv.injective
  have h := intervalι_vertices.{u} T a b hab
    (ULift.up 0 : Vertices.{u} (intervalCode T a b hab))
  simpa only [mapVertices, first, intervalEmbedding_first, Equiv.apply_symm_apply] using h

theorem intervalι_last :
    (intervalι.{u} T a b hab).app _ (intervalCode T a b hab).last =
      T.verticesEquiv.symm (ULift.up b) := by
  apply T.verticesEquiv.injective
  have h := intervalι_vertices.{u} T a b hab
    (ULift.up (Fin.last (b.val - a.val)) : Vertices.{u} (intervalCode T a b hab))
  simpa only [mapVertices, last, intervalEmbedding_last, Equiv.apply_symm_apply] using h

theorem intervalι_operator {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌)
    (x : (toSSet.{u} (intervalCode T a b hab)).obj (op ⦋n⦌)) :
    (intervalι T a b hab).app _ ((toSSet (intervalCode T a b hab)).map α.op x) =
      (toSSet T).map α.op ((intervalι T a b hab).app _ x) :=
  congrFun ((intervalι T a b hab).naturality α.op) x

end

end DaggerChosenRigidificationNecklace.NecklaceCode
