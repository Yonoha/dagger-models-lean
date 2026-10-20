import OriginalCounitRightConeRelativeHomotopyEndpoints

/-!
# Time one and formal endpoints of the actual cone homotopy

The time-one map is compared with the already chosen `projection ≫ lastEdge`
on both legs of the literal pushout. This source-only candidate does not
derive a weak equivalence from the simplicial homotopy.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRelativeHomotopy

universe u

namespace DaggerOriginalCounitRightConeRelativeHomotopy

noncomputable section

/-- The existing projection and last-edge maps give the time-one ordinal map. -/
theorem prismOrder_one_projection (n : ℕ) (i : Fin (n + 2)) :
    prismOrder n 1 (i, 1) =
      (projectionHom n ≫ lastEdgeHom n).toOrderHom i := by
  cases i using Fin.lastCases with
  | cast j =>
      have hj : j.castSucc = Fin.castAdd 1 j := rfl
      rw [hj]
      apply Fin.ext
      simp [prismOrder, projectionHom, lastEdgeHom,
        AugmentedSimplexCategory.tensorHomOf, Fin.addCases_left]
      change max (j : ℕ) n = n
      omega
  | last =>
      have hl : Fin.last (n + 1) = Fin.natAdd (n + 1) (0 : Fin 1) := by
        apply Fin.ext
        rfl
      rw [hl]
      apply Fin.ext
      simp [prismOrder, projectionHom, lastEdgeHom,
        AugmentedSimplexCategory.tensorHomOf, Fin.addCases_right]
      rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl, Fin.addCases_right]
      rfl

/-- The whole large-simplex time-one map is the existing projection section. -/
theorem simplexPrism_time_one (n : ℕ) :
    timeSlice.{u} Δ[n + 1] 1 ≫ simplexPrism.{u} n 1 =
      SSet.stdSimplex.map (projectionHom n ≫ lastEdgeHom n) := by
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d =>
    apply SSet.stdSimplex.ext
    intro i
    change (simplexPrism.{u} n 1).app (op ⦋d⦌)
      (x, SSet.stdSimplex.const 1 1 (op ⦋d⦌)) i =
        (projectionHom n ≫ lastEdgeHom n).toOrderHom (x i)
    rw [simplexPrism_app]
    change prismOrder n 1 (x i, 1) =
      (projectionHom n ≫ lastEdgeHom n).toOrderHom (x i)
    exact prismOrder_one_projection n (x i)

/-- The first end of the existing last edge is on the collapsed face. -/
theorem firstVertex_lastEdge_base (n : ℕ) :
    SSet.stdSimplex.map firstVertexHom ≫
        SSet.stdSimplex.map (lastEdgeHom n) ≫ simplexIncl.{u} n =
      baseIncl.{u} n := by
  let v : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)
  have h := AugmentedSimplexCategory.inl_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map v)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋0⦌))
  change firstVertexHom ≫ lastEdgeHom n =
    v ≫ AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ at h
  calc
    _ = SSet.stdSimplex.map (v ≫
          AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌) ≫
            simplexIncl.{u} n := by
      simp only [← Category.assoc, ← Functor.map_comp, h]
    _ = SSet.stdSimplex.map v ≫ face.{u} n ≫ simplexIncl.{u} n := by
      simp only [face_eq_inl, Functor.map_comp, ← Category.assoc]
    _ = SSet.stdSimplex.map v ≫ collapse.{u} n ≫ baseIncl.{u} n := by
      rw [face_eq_collapse]
    _ = baseIncl.{u} n := by
      have hv : SSet.stdSimplex.map v ≫ collapse.{u} n =
          𝟙 (Δ[0] : SSet.{u}) := SSet.stdSimplex.ext₀
      rw [← Category.assoc, hv, Category.id_comp]

/-- Time one on the literal pushout is the chosen projection followed by
the chosen last-edge section, as an equality of whole simplicial maps. -/
theorem relativeHomotopy_time_one (n : ℕ) :
    timeSlice.{u} (cone.{u} n) 1 ≫ relativeHomotopy.{u} n =
      projection.{u} n ≫ lastEdge.{u} n := by
  apply pushout.hom_ext
  · calc
      simplexIncl.{u} n ≫ timeSlice.{u} (cone.{u} n) 1 ≫
          relativeHomotopy.{u} n =
        timeSlice.{u} Δ[n + 1] 1 ≫
          (simplexIncl.{u} n ▷ (Δ[1] : SSet.{u})) ≫
            relativeHomotopy.{u} n := by
        simp only [← Category.assoc]
        rw [timeSlice_naturality]
      _ = SSet.stdSimplex.map (projectionHom n ≫ lastEdgeHom n) ≫
            simplexIncl.{u} n := by
        rw [simplexIncl_relativeHomotopy, ← Category.assoc,
          simplexPrism_time_one]
      _ = simplexIncl.{u} n ≫ projection.{u} n ≫ lastEdge.{u} n := by
        simp only [← Category.assoc, simplexIncl_projection, lastEdge,
          ← Functor.map_comp]
  · calc
      baseIncl.{u} n ≫ timeSlice.{u} (cone.{u} n) 1 ≫
          relativeHomotopy.{u} n =
        timeSlice.{u} Δ[0] 1 ≫
          (baseIncl.{u} n ▷ (Δ[1] : SSet.{u})) ≫
            relativeHomotopy.{u} n := by
        simp only [← Category.assoc]
        rw [timeSlice_naturality]
      _ = baseIncl.{u} n := by
        rw [baseIncl_relativeHomotopy, ← Category.assoc]
        have h : timeSlice.{u} Δ[0] 1 ≫
            SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ Δ[1]) : SSet.{u}) =
              𝟙 (Δ[0] : SSet.{u}) := SSet.stdSimplex.ext₀
        rw [h, Category.id_comp]
      _ = baseIncl.{u} n ≫ projection.{u} n ≫ lastEdge.{u} n := by
        simpa only [← Category.assoc, baseIncl_projection, lastEdge] using
          (firstVertex_lastEdge_base.{u} n).symm

/-- The formal alpha endpoint is fixed for the whole interval. -/
theorem alpha_relativeHomotopy (n : ℕ) :
    (alphaMap.{u} n ▷ (Δ[1] : SSet.{u})) ≫ relativeHomotopy.{u} n =
      SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ Δ[1]) : SSet.{u}) ≫
        alphaMap.{u} n :=
  baseIncl_relativeHomotopy.{u} n

/-- The actual last vertex is fixed in every degree of the large prism. -/
theorem lastVertex_prism (n : ℕ) :
    (lastVertex.{u} n ▷ (Δ[1] : SSet.{u})) ≫ simplexPrism.{u} n 1 =
      SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ Δ[1]) : SSet.{u}) ≫
        lastVertex.{u} n := by
  apply NatTrans.ext
  funext q z
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d =>
    apply SSet.stdSimplex.ext
    intro i
    change prismOrder n 1 (Fin.last (n + 1), z.2 i) = Fin.last (n + 1)
    exact prismOrder_last n (z.2 i)

/-- The distinct formal omega endpoint is also fixed for the whole interval. -/
theorem omega_relativeHomotopy (n : ℕ) :
    (omegaMap.{u} n ▷ (Δ[1] : SSet.{u})) ≫ relativeHomotopy.{u} n =
      SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ Δ[1]) : SSet.{u}) ≫
        omegaMap.{u} n := by
  rw [omegaMap, MonoidalCategory.comp_whiskerRight_assoc,
    simplexIncl_relativeHomotopy]
  simp only [← Category.assoc]
  rw [lastVertex_prism]

end

end DaggerOriginalCounitRightConeRelativeHomotopy
