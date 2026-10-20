import OriginalRightOuterHornExtensionality

/-!
# Exact boundary edge and fixed-prefix vertex extracted from an original right outer horn

The supplied suffix-zero face chooses the original fixed prefix and target vertex.
The supplied whole prefix boundary is an actual edge in the boundary mapping presheaf.
Its target is the restriction of that same coslice vertex, and its suffix image is
exactly the last edge of the original horn.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedBoundaryRestriction DaggerOriginalJoinedBoundaryProjection
open DaggerOriginalJoinedBoundarySuffixInclusion DaggerOriginalRightOuterHornInclusions

universe u

namespace DaggerOriginalRightOuterHornData

noncomputable section

/-- The supplied whole prefix boundary is the original boundary-presheaf one-simplex. -/
def rightOuterBoundaryData {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X) :
    (boundaryJoinedPresheaf k X).obj (op ⦋1⦌) :=
  rightOuterBoundaryInclusion k ≫ φ

/-- The supplied suffix-zero face is the original joined zero-simplex. -/
def rightOuterRawVertex {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X) :
    (joinedPresheaf ⦋k⦌ X).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (X := X) (n := ⦋k + 1⦌) (rightOuterJoinedFaceInclusion k ≫ φ)

/-- The fixed prefix is the actual left-block restriction of the supplied face. -/
def rightOuterPrefix {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X) : X.obj (op ⦋k⦌) :=
  X.map (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋0⦌).op (rightOuterRawVertex k φ)

/-- The supplied face, with its actual original prefix, is the prescribed coslice vertex. -/
def rightOuterCosliceVertex {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X) :
    (simplexCoslice ⦋k⦌ X (rightOuterPrefix k φ)).obj (op ⦋0⦌) :=
  ⟨rightOuterRawVertex k φ, rfl⟩

/-- The target of the original boundary edge is precisely the prescribed vertex restriction. -/
theorem rightOuterBoundaryData_target {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X) :
    (boundaryJoinedPresheaf k X).δ 0 (rightOuterBoundaryData k φ) =
      (cosliceBoundaryRestriction k X (rightOuterPrefix k φ)).app (op ⦋0⦌)
        (rightOuterCosliceVertex k φ) := by
  change prefixBoundaryMap k (SimplexCategory.δ (n := 0) 0) ≫
    (rightOuterBoundaryInclusion k ≫ φ) = (prefixBoundary k 0).ι ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (rightOuterJoinedFaceInclusion k ≫ φ))
  rw [Equiv.symm_apply_apply, ← Category.assoc, rightOuterBoundary_face_square,
    Category.assoc]

/-- The whole original boundary gives an edge with the exact original prescribed target. -/
def rightOuterBoundaryEdge {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X) :
    SSet.Edge ((boundaryJoinedPresheaf k X).δ 1 (rightOuterBoundaryData k φ))
      ((cosliceBoundaryRestriction k X (rightOuterPrefix k φ)).app (op ⦋0⦌)
        (rightOuterCosliceVertex k φ)) :=
  ⟨rightOuterBoundaryData k φ, rfl, rightOuterBoundaryData_target k φ⟩

/-- The projected edge is exactly the last edge of the actual original horn. -/
theorem rightOuterBoundaryEdge_image {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ X) :
    ((rightOuterBoundaryEdge k φ).map (boundaryProjection k X)).edge =
      SSet.yonedaEquiv (rightOuterLastEdgeInclusion k ≫ φ) := by
  change SSet.yonedaEquiv (boundarySuffixInclusion k ⦋1⦌ ≫
    (rightOuterBoundaryInclusion k ≫ φ)) =
      SSet.yonedaEquiv ((boundarySuffixInclusion k ⦋1⦌ ≫
        rightOuterBoundaryInclusion k) ≫ φ)
  rw [Category.assoc]

end

end DaggerOriginalRightOuterHornData
