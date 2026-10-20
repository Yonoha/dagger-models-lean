import ActualRightConeFinalEdgeMaps
import NativeRightConeCofaceGeometry

/-! The original cone projection respects ALL cosimplicial cone maps. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerActualRightConeFinalEdgeMaps DaggerNativeRightConeCofaceGeometry
universe u
namespace DaggerActualRightConeProjectionNaturality
noncomputable section

theorem height_prefix (n : ℕ) (i : Fin (n + 1)) :
    (heightHom n).toOrderHom i.castSucc = (0 : Fin 2) := by
  apply Fin.ext
  change (if i.val = n + 1 then 1 else 0) = 0
  have hi := i.isLt
  split_ifs <;> omega

theorem height_last (n : ℕ) :
    (heightHom n).toOrderHom (Fin.last (n + 1)) = (1 : Fin 2) := by
  apply Fin.ext
  change (if n + 1 = n + 1 then 1 else 0) = 1
  rw [if_pos rfl]

theorem join_height {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap.{u} α ≫ heightMap n = heightMap m := by
  rw [joinMap, heightMap, heightMap, ← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (heightHom n).toOrderHom ((joinHom α).toOrderHom i) =
    (heightHom m).toOrderHom i
  induction i using Fin.lastCases with
  | last =>
      change (heightHom n).toOrderHom ((joinHom α).toOrderHom (Fin.last (m + 1))) =
        (heightHom m).toOrderHom (Fin.last (m + 1))
      rw [joinHom_last, height_last, height_last]
  | cast i => rw [joinHom_prefix, height_prefix, height_prefix]

theorem projection_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    coneMap.{u} α ≫ projection n.len = projection m.len := by
  induction m using SimplexCategory.rec with | h m =>
    induction n using SimplexCategory.rec with | h n =>
      have hI := simplexIncl_naturality.{u} α
      have hB := baseIncl_naturality.{u} α
      simp only [SimplexCategory.len_mk] at hI hB
      apply pushout.hom_ext
      · change simplexIncl m ≫ (coneMap α ≫ projection n) = simplexIncl m ≫ projection m
        rw [← Category.assoc, hI, Category.assoc,
          simplex_projection, join_height, simplex_projection]
      · change baseIncl m ≫ (coneMap α ≫ projection n) = baseIncl m ≫ projection m
        rw [← Category.assoc, hB]
        change alphaMap n ≫ projection n = alphaMap m ≫ projection m
        rw [alpha_projection, alpha_projection]

end
end DaggerActualRightConeProjectionNaturality
