import ChosenNecklaceTargetJoints

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {S T : NecklaceCode} (f : toSSet.{u} S ⟶ toSSet.{u} T)

theorem necklaceMap_vertex_bounds (x : S.toSSet.obj (op ⦋0⦌)) :
    orderMap f 0 ≤ T.inclusion.app _ (f.app _ x) 0 ∧
      T.inclusion.app _ (f.app _ x) 0 ≤ orderMap f (Fin.last S.len) := by
  let v := (S.verticesEquiv x).down
  have hl := (orderMap f).monotone (Fin.zero_le v)
  have hr := (orderMap f).monotone (Fin.le_last v)
  have he : orderMap f v = T.inclusion.app _ (f.app _ x) 0 := by
    dsimp [v, orderMap, mapVertices]
    rw [S.verticesEquiv.symm_apply_apply]
    rfl
  rw [he] at hl hr
  exact ⟨hl, hr⟩

variable (a b : Fin (S.len + 1)) (hab : a ≤ b)
  (c d : Fin (T.len + 1)) (hcd : c ≤ d)
  (hc : c ≤ orderMap f a) (hd : orderMap f b ≤ d)

theorem intervalRestriction_first :
    orderMap (intervalι S a b hab ≫ f) 0 = orderMap f a := by
  rw [orderMap_comp_apply]
  congr 1
  change (mapVertices (intervalι S a b hab) (ULift.up 0)).down = a
  rw [intervalι_vertices, intervalEmbedding_first]

theorem intervalRestriction_last :
    orderMap (intervalι S a b hab ≫ f) (Fin.last (intervalCode S a b hab).len) =
      orderMap f b := by
  rw [orderMap_comp_apply]
  congr 1
  change (mapVertices (intervalι S a b hab) (ULift.up (Fin.last _))).down = b
  rw [intervalι_vertices]
  exact intervalEmbedding_last S a b hab

include hc hd in
theorem intervalRestriction_bounds (x : (intervalCode S a b hab).toSSet.obj (op ⦋0⦌)) :
    c ≤ T.inclusion.app _ ((intervalι S a b hab ≫ f).app _ x) 0 ∧
      T.inclusion.app _ ((intervalι S a b hab ≫ f).app _ x) 0 ≤ d := by
  have h := necklaceMap_vertex_bounds (intervalι S a b hab ≫ f) x
  rw [intervalRestriction_first, intervalRestriction_last] at h
  exact ⟨hc.trans h.1, h.2.trans hd⟩

/-- Restrict an actual necklace map to any source and target intervals with the stated bounds. -/
def necklaceIntervalMap : (intervalCode S a b hab).toSSet ⟶
    (intervalCode T c d hcd).toSSet :=
  intervalFactor T c d hcd (intervalι S a b hab ≫ f)
    (intervalRestriction_bounds f a b hab c d hc hd)

theorem necklaceIntervalMap_fac :
    necklaceIntervalMap f a b hab c d hcd hc hd ≫ intervalι T c d hcd =
      intervalι S a b hab ≫ f :=
  intervalFactor_fac T c d hcd _ _

end

end DaggerOriginalProductGadget
