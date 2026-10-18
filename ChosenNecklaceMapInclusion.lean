import ChosenNecklaceOrderMaps

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

/-- Every actual map, not only endpoint-preserving maps, retains the original ambient operator. -/
theorem map_inclusion {T U : NecklaceCode} (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    f ≫ U.inclusion = T.inclusion ≫ SSet.stdSimplex.map
      (SimplexCategory.Hom.mk (orderMap f) : ⦋T.len⦌ ⟶ ⦋U.len⦌) := by
  apply stdSimplex_hom_ext
  intro x
  apply SSet.stdSimplex.obj₀Equiv.injective
  change SSet.stdSimplex.obj₀Equiv (U.inclusion.app _ (f.app _ x)) =
    orderMap f (SSet.stdSimplex.obj₀Equiv (T.inclusion.app _ x))
  change (U.verticesEquiv (f.app _ x)).down =
    (mapVertices f (ULift.up ((T.verticesEquiv x).down))).down
  have hx : ULift.up ((T.verticesEquiv x).down) = T.verticesEquiv x := rfl
  rw [hx]
  simp only [mapVertices, Equiv.symm_apply_apply]

end

end DaggerChosenRigidificationNecklace.NecklaceCode
