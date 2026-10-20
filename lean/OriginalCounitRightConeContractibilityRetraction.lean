import OriginalCounitRightConeFunctor

/-!
# An actual edge retraction of every original right cone

The quotient cone admits a map to the standard edge, split by its final
edge. This does not assert that the cone map is a Joyal equivalence or that
the original rigidification Hom `Q n` is weakly contractible.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor

universe u

namespace DaggerOriginalCounitRightConeContractibilityRetraction

noncomputable section

/-- The first vertex of the standard edge, as an ordinal-sum inclusion. -/
def firstVertexHom : ⦋0⦌ ⟶ ⦋1⦌ :=
  AugmentedSimplexCategory.inl' (SimplexCategory.mk 0) (SimplexCategory.mk 0)

/-- Collapse the initial `n + 1` vertices and retain the final vertex. -/
def projectionHom (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋1⦌ :=
  AugmentedSimplexCategory.tensorHomOf
    (SimplexCategory.isTerminalZero.from ⦋n⦌) (𝟙 ⦋0⦌)

/-- The last edge, from vertex `n` to vertex `n + 1`. -/
def lastEdgeHom (n : ℕ) : ⦋1⦌ ⟶ ⦋n + 1⦌ :=
  AugmentedSimplexCategory.tensorHomOf
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) (𝟙 ⦋0⦌)

/-- The projection has the attaching-face value prescribed by the pushout. -/
theorem projection_face (n : ℕ) :
    face.{u} n ≫ SSet.stdSimplex.map (projectionHom n) =
      collapse.{u} n ≫ SSet.stdSimplex.map firstVertexHom := by
  rw [face_eq_inl]
  have hc : collapse.{u} n =
      SSet.stdSimplex.map (SimplexCategory.isTerminalZero.from ⦋n⦌) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hc]
  simp only [← Functor.map_comp]
  congr 1
  have h := AugmentedSimplexCategory.inl_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map
      (SimplexCategory.isTerminalZero.from ⦋n⦌))
    (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋0⦌))
  change AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ ≫ projectionHom n =
    (SimplexCategory.isTerminalZero.from ⦋n⦌) ≫ firstVertexHom at h
  exact h

/-- The map from the literal quotient cone to the standard edge. -/
def projection (n : ℕ) : cone.{u} n ⟶ (Δ[1] : SSet.{u}) :=
  desc.{u} n (SSet.stdSimplex.map (projectionHom n))
    (SSet.stdSimplex.map firstVertexHom) (projection_face.{u} n)

theorem simplexIncl_projection (n : ℕ) :
    simplexIncl.{u} n ≫ projection.{u} n =
      SSet.stdSimplex.map (projectionHom n) :=
  simplexIncl_desc.{u} n _ _ _

theorem baseIncl_projection (n : ℕ) :
    baseIncl.{u} n ≫ projection.{u} n =
      SSet.stdSimplex.map firstVertexHom :=
  baseIncl_desc.{u} n _ _ _

/-- The section is the actual last edge inside the large simplex. -/
def lastEdge (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ cone.{u} n :=
  SSet.stdSimplex.map (lastEdgeHom n) ≫ simplexIncl.{u} n

theorem lastEdgeHom_projectionHom (n : ℕ) :
    lastEdgeHom n ≫ projectionHom n = 𝟙 ⦋1⦌ := by
  have hc : SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n) ≫
      SimplexCategory.isTerminalZero.from ⦋n⦌ = 𝟙 ⦋0⦌ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)))
    (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋0⦌))
    (AugmentedSimplexCategory.inclusion.map
      (SimplexCategory.isTerminalZero.from ⦋n⦌))
    (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋0⦌))
  change lastEdgeHom n ≫ projectionHom n =
    AugmentedSimplexCategory.tensorHomOf
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n) ≫
        SimplexCategory.isTerminalZero.from ⦋n⦌) (𝟙 ⦋0⦌ ≫ 𝟙 ⦋0⦌) at h
  rw [hc, Category.id_comp] at h
  have hid := AugmentedSimplexCategory.tensor_id
    (AugmentedSimplexCategory.inclusion.obj ⦋0⦌)
    (AugmentedSimplexCategory.inclusion.obj ⦋0⦌)
  change AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌) (𝟙 ⦋0⦌) =
    𝟙 ⦋1⦌ at hid
  exact h.trans hid

/-- The original last edge is a section of the cone-to-edge projection. -/
theorem lastEdge_projection (n : ℕ) :
    lastEdge.{u} n ≫ projection.{u} n = 𝟙 (Δ[1] : SSet.{u}) := by
  rw [lastEdge, Category.assoc, simplexIncl_projection]
  rw [← Functor.map_comp, lastEdgeHom_projectionHom]
  exact CategoryTheory.Functor.map_id SSet.stdSimplex ⦋1⦌

end

end DaggerOriginalCounitRightConeContractibilityRetraction
