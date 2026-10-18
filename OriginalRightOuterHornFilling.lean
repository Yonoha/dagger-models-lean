import OriginalRightOuterHornData

/-!
# Filling the original right outer horn with invertible original last edge

Lift the actual whole-boundary edge into the coslice of the actual supplied prefix,
with the original supplied suffix-zero face as prescribed target. The resulting
original joined one-simplex restricts to both supplied pieces. Native horn
extensionality proves the full original horn extension in every dimension at
least two and every universe, assuming only inner fillers and the original
last-edge invertibility.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedBoundaryRestriction DaggerOriginalJoinedBoundaryProjection
open DaggerOriginalOrdinaryKanCoreEdgeMembership DaggerOriginalInnerHornFillers
open DaggerOriginalAllPrefixBoundaryInvertibleLifting
open DaggerOriginalRightOuterHornInclusions DaggerOriginalRightOuterHornExtensionality
open DaggerOriginalRightOuterHornData

universe u

namespace DaggerOriginalRightOuterHornFilling

noncomputable section

/-- The lifted original coslice edge is the actual original ambient filling simplex. -/
def rightOuterSimplexFromEdge {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X)
    {a : (simplexCoslice ⦋k⦌ X (rightOuterPrefix k φ)).obj (op ⦋0⦌)}
    (g : SSet.Edge a (rightOuterCosliceVertex k φ)) : (Δ[k + 2] : SSet.{u}) ⟶ X :=
  (SSet.yonedaEquiv (X := X) (n := ⦋k + 2⦌)).symm g.edge.val

/-- The filling preserves the supplied whole original prefix-boundary map. -/
theorem rightOuterSimplexFromEdge_boundary {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X)
    {a : (simplexCoslice ⦋k⦌ X (rightOuterPrefix k φ)).obj (op ⦋0⦌)}
    (g : SSet.Edge a (rightOuterCosliceVertex k φ))
    (hg : (cosliceBoundaryRestriction k X (rightOuterPrefix k φ)).app (op ⦋1⦌) g.edge =
      (rightOuterBoundaryEdge k φ).edge) :
    (prefixBoundary k 1).ι ≫ rightOuterSimplexFromEdge k φ g =
      rightOuterBoundaryInclusion k ≫ φ := by
  exact hg

/-- The filling preserves the exact original supplied suffix-zero face. -/
theorem rightOuterSimplexFromEdge_face {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X)
    {a : (simplexCoslice ⦋k⦌ X (rightOuterPrefix k φ)).obj (op ⦋0⦌)}
    (g : SSet.Edge a (rightOuterCosliceVertex k φ)) :
    SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ (n := 0) 0)) ≫
      rightOuterSimplexFromEdge k φ g = rightOuterJoinedFaceInclusion k ≫ φ := by
  apply (SSet.yonedaEquiv (X := X) (n := ⦋k + 1⦌)).injective
  have hy : SSet.yonedaEquiv (X := X) (n := ⦋k + 2⦌)
      (rightOuterSimplexFromEdge k φ g) = g.edge.val := Equiv.apply_symm_apply _ _
  rw [yonedaEquiv_precomp_operator]
  have h := congrArg Subtype.val g.tgt_eq
  change X.map ((ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ (n := 0) 0)).op
    g.edge.val = rightOuterRawVertex k φ at h
  exact (congrArg (X.map ((ordinalJoinLeft ⦋k⦌).map
    (SimplexCategory.δ (n := 0) 0)).op) hy).trans h

/-- The two exact supplied restrictions recover the entire actual original right outer horn. -/
theorem rightOuterSimplexFromEdge_horn {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X)
    {a : (simplexCoslice ⦋k⦌ X (rightOuterPrefix k φ)).obj (op ⦋0⦌)}
    (g : SSet.Edge a (rightOuterCosliceVertex k φ))
    (hg : (cosliceBoundaryRestriction k X (rightOuterPrefix k φ)).app (op ⦋1⦌) g.edge =
      (rightOuterBoundaryEdge k φ).edge) :
    φ = Λ[k + 2, Fin.last (k + 2)].ι ≫ rightOuterSimplexFromEdge k φ g := by
  apply rightOuterHorn_hom_ext k
  · rw [← Category.assoc, rightOuterBoundaryInclusion_comp]
    exact (rightOuterSimplexFromEdge_boundary k φ g hg).symm
  · rw [← Category.assoc, rightOuterJoinedFaceInclusion_comp]
    exact (rightOuterSimplexFromEdge_face k φ g).symm

/-- An actual right outer horn whose original last edge is invertible extends to an original
simplex, for every original dimension at least two and every universe. -/
theorem right_outer_horn_filler {X : SSet.{u}} (hX : innerHornFillers X) (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X)
    (he : edgeIsInvertible X (SSet.yonedaEquiv (rightOuterLastEdgeInclusion k ≫ φ))) :
    ∃ σ : (Δ[k + 2] : SSet.{u}) ⟶ X, φ = Λ[k + 2, Fin.last (k + 2)].ι ≫ σ := by
  have he' : edgeIsInvertible X
      ((rightOuterBoundaryEdge k φ).map (boundaryProjection k X)).edge := by
    rw [rightOuterBoundaryEdge_image]
    exact he
  obtain ⟨a, _, g, hg, _⟩ := coslice_boundary_lift_invertible_image_edge_to_target
    hX k (rightOuterPrefix k φ) (rightOuterCosliceVertex k φ) (rightOuterBoundaryEdge k φ) he'
  exact ⟨rightOuterSimplexFromEdge k φ g, rightOuterSimplexFromEdge_horn k φ g hg⟩

end

end DaggerOriginalRightOuterHornFilling
