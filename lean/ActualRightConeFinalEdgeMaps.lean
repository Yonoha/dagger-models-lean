import NativeRightConeFinalEdge

/-! The original right cone retracts onto its actual last-initial-vertex edge. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerNativeRightConeFinalEdge
universe u
namespace DaggerActualRightConeFinalEdgeMaps
noncomputable section

def heightHom (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom
    ⟨fun i ↦ ⟨if i.val = n + 1 then 1 else 0, by split_ifs <;> omega⟩, by
      intro i j hij
      change (if i.val = n + 1 then 1 else 0) ≤ (if j.val = n + 1 then 1 else 0)
      have hi := i.isLt
      have hj := j.isLt
      change i.val ≤ j.val at hij
      split_ifs <;> omega⟩

def heightMap (n : ℕ) : (Δ[n + 1] : SSet.{u}) ⟶ Δ[1] :=
  SSet.stdSimplex.map (heightHom n)

theorem collapse_eq_map (n : ℕ) : collapse.{u} n =
    SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

theorem face_height (n : ℕ) : face.{u} n ≫ heightMap n =
    collapse n ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
  rw [collapse_eq_map]
  change SSet.stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1))) ≫
    SSet.stdSimplex.map (heightHom n) =
    SSet.stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) ≫
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  ext i : 3
  apply Fin.ext
  change (if ((Fin.last (n + 1)).succAbove i).val = n + 1 then 1 else 0) = 0
  rw [Fin.succAbove_last]
  simp only [Fin.val_castSucc]
  have hi : i.val < n + 1 := i.isLt
  split_ifs <;> omega

theorem edge_height (n : ℕ) : edgeMap.{u} n ≫ heightMap n = 𝟙 (Δ[1] : SSet.{u}) := by
  rw [edgeMap, heightMap, ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_id]
  apply congrArg SSet.stdSimplex.map
  ext i : 3
  apply Fin.ext
  change (if n + i.val = n + 1 then 1 else 0) = i.val
  have hi : i.val < 2 := i.isLt
  split_ifs <;> omega

def projection (n : ℕ) : cone.{u} n ⟶ Δ[1] :=
  desc n (heightMap n) (SSet.stdSimplex.δ (1 : Fin 2)) (face_height n)

def sectionMap (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ cone n := edgeMap n ≫ simplexIncl n

theorem simplex_projection (n : ℕ) : simplexIncl.{u} n ≫ projection n = heightMap n :=
  simplexIncl_desc _ _ _ _

theorem alpha_projection (n : ℕ) : alphaMap.{u} n ≫ projection n =
    SSet.stdSimplex.δ (1 : Fin 2) := baseIncl_desc _ _ _ _

theorem first_section (n : ℕ) : SSet.stdSimplex.δ (1 : Fin 2) ≫ sectionMap.{u} n =
    alphaMap n := by
  rw [sectionMap, ← Category.assoc, edgeMap_first, Category.assoc, face_eq_collapse,
    ← Category.assoc]
  have ht : prefixLast.{u} n ≫ collapse n = 𝟙 (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht, Category.id_comp]
  rfl

theorem last_section (n : ℕ) : SSet.stdSimplex.δ (0 : Fin 2) ≫ sectionMap.{u} n =
    omegaMap n := by
  rw [sectionMap, ← Category.assoc, edgeMap_last]
  rfl

theorem section_projection (n : ℕ) : sectionMap.{u} n ≫ projection n = 𝟙 (Δ[1] : SSet.{u}) := by
  rw [sectionMap, Category.assoc, simplex_projection, edge_height]

theorem omega_projection (n : ℕ) : omegaMap.{u} n ≫ projection n =
    SSet.stdSimplex.δ (0 : Fin 2) := by
  rw [← last_section, Category.assoc, section_projection, Category.comp_id]

end
end DaggerActualRightConeFinalEdgeMaps
