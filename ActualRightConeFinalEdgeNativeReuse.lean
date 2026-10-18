import ActualRightConeFinalEdgeWeak
import ActualRightConeProjectionNaturality
import OriginalCounitRightConeContractibilityRetraction

/-! Identify the coordinate proof with the EXISTING original projection and original last edge. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerNativeRightConeFinalEdge DaggerNativeRightConeCofaceGeometry
open DaggerActualRightConeFinalEdgeMaps DaggerActualRightConeFinalEdgeWeak
open DaggerActualRightConeProjectionNaturality DaggerNativeJoyalMappingTest
universe u
namespace DaggerActualRightConeFinalEdgeNativeReuse
noncomputable section

private abbrev O := DaggerOriginalCounitRightConeContractibilityRetraction.projectionHom

theorem heightHom_eq_native (n : ℕ) : heightHom n = O n := by
  let α := SimplexCategory.isTerminalZero.from ⦋n⦌
  change heightHom n = joinHom α
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  induction i using Fin.lastCases with
  | last =>
      change (heightHom n).toOrderHom (Fin.last (n + 1)) =
        (joinHom α).toOrderHom (Fin.last (n + 1))
      rw [height_last, joinHom_last]
      rfl
  | cast j =>
      have hp := joinHom_prefix α j
      have hz : α.toOrderHom j = (0 : Fin 1) :=
        congrArg (fun β : ⦋n⦌ ⟶ ⦋0⦌ ↦ β.toOrderHom j)
          (SimplexCategory.isTerminalZero.hom_ext α
            (SimplexCategory.const ⦋n⦌ ⦋0⦌ (0 : Fin 1)))
      exact (height_prefix n j).trans ((congrArg Fin.castSucc hz).symm.trans hp.symm)

theorem edgeHom_eq_native (n : ℕ) : edgeHom n =
    DaggerOriginalCounitRightConeContractibilityRetraction.lastEdgeHom n := by
  ext i : 3
  fin_cases i <;> rfl

theorem projection_eq_native (n : ℕ) : projection.{u} n =
    DaggerOriginalCounitRightConeContractibilityRetraction.projection n := by
  apply pushout.hom_ext
  · change simplexIncl n ≫ projection n = simplexIncl n ≫
      DaggerOriginalCounitRightConeContractibilityRetraction.projection n
    rw [simplex_projection,
      DaggerOriginalCounitRightConeContractibilityRetraction.simplexIncl_projection,
      heightMap, heightHom_eq_native]
  · change alphaMap n ≫ projection n = baseIncl n ≫
      DaggerOriginalCounitRightConeContractibilityRetraction.projection n
    rw [alpha_projection,
      DaggerOriginalCounitRightConeContractibilityRetraction.baseIncl_projection]
    change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) = _
    apply congrArg SSet.stdSimplex.map
    ext i : 3
    fin_cases i
    rfl

theorem section_eq_native (n : ℕ) : sectionMap.{u} n =
    DaggerOriginalCounitRightConeContractibilityRetraction.lastEdge n := by
  unfold sectionMap DaggerOriginalCounitRightConeContractibilityRetraction.lastEdge
  rw [edgeMap, edgeHom_eq_native]

theorem native_projection_categorical_weak (n : ℕ) : weakCategoricalEquivalences
    (DaggerOriginalCounitRightConeContractibilityRetraction.projection.{u} n) := by
  rw [← projection_eq_native]
  exact projection_categorical_weak n

theorem native_lastEdge_categorical_weak (n : ℕ) : weakCategoricalEquivalences
    (DaggerOriginalCounitRightConeContractibilityRetraction.lastEdge.{u} n) := by
  rw [← section_eq_native]
  exact section_categorical_weak n

theorem native_projection_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    coneMap.{u} α ≫ DaggerOriginalCounitRightConeContractibilityRetraction.projection n.len =
      DaggerOriginalCounitRightConeContractibilityRetraction.projection m.len := by
  rw [← projection_eq_native, ← projection_eq_native]
  exact projection_naturality α

end
end DaggerActualRightConeFinalEdgeNativeReuse
