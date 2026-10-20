import OriginalAllPrefixBoundaryProjectionLifting
import OriginalRelativeInvertibleEdgeTargetLift

/-!
# Original whole-boundary invertibility and prescribed-target coslice lifts

The proved original boundary projection lifts all nonfinal horns. Its native
relative two-horn property reflects the original unit-based invertibility.
Native exact target-edge lifting applies both to the boundary projection and
to the original fixed-prefix coslice restriction over its now verified inner
boundary presheaf. The original prefix, target vertex and edge image are retained.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreEdgeMembership DaggerOriginalInnerHornFillers
open DaggerOriginalSimplexCoslice DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedBoundaryProjection DaggerOriginalCosliceLeftLiftingProperty
open DaggerOriginalRelativeLeftTwoHornInverses DaggerOriginalRelativeInvertibleEdgeTargetLift
open DaggerOriginalAllPrefixBoundaryProjectionLifting

universe u

namespace DaggerOriginalAllPrefixBoundaryInvertibleLifting

noncomputable section

/-- The original whole-boundary projection reflects original unit-based edge invertibility. -/
theorem boundary_projection_reflects_invertible_edge {X : SSet.{u}} (hX : innerHornFillers X)
    (k : ℕ) {a b : (boundaryJoinedPresheaf k X).obj (op ⦋0⦌)} (e : SSet.Edge a b)
    (he : edgeIsInvertible X (e.map (boundaryProjection k X)).edge) :
    edgeIsInvertible (boundaryJoinedPresheaf k X) e.edge := by
  haveI := boundaryProjection_hasLiftingProperty hX k 1 0 (by decide)
  exact edgeIsInvertible_of_invertible_image (boundaryProjection k X) hX e he

/-- The original boundary projection lifts an invertible edge to the specified actual vertex,
retaining the exact original one-simplex image. -/
theorem boundary_projection_lift_invertible_edge_to_target {X : SSet.{u}}
    (hX : innerHornFillers X) (k : ℕ) (b : (boundaryJoinedPresheaf k X).obj (op ⦋0⦌))
    {x : X.obj (op ⦋0⦌)} (e : SSet.Edge x ((boundaryProjection k X).app (op ⦋0⦌) b))
    (he : edgeIsInvertible X e.edge) :
    ∃ a : (boundaryJoinedPresheaf k X).obj (op ⦋0⦌),
      (boundaryProjection k X).app (op ⦋0⦌) a = x ∧
      ∃ g : SSet.Edge a b, (boundaryProjection k X).app (op ⦋1⦌) g.edge = e.edge ∧
        edgeIsInvertible (boundaryJoinedPresheaf k X) g.edge := by
  haveI := boundaryProjection_hasLiftingProperty hX k 0 0 (by decide)
  haveI := boundaryProjection_hasLiftingProperty hX k 1 0 (by decide)
  exact lift_invertible_edge_to_target (boundaryProjection k X) hX b e he

/-- The original fixed-prefix coslice restriction lifts a boundary edge with invertible original
suffix image to the specified actual coslice vertex, keeping the prefix and edge image. -/
theorem coslice_boundary_lift_invertible_image_edge_to_target {X : SSet.{u}}
    (hX : innerHornFillers X) (k : ℕ) (f : X.obj (op ⦋k⦌))
    (b : (simplexCoslice ⦋k⦌ X f).obj (op ⦋0⦌))
    {x : (boundaryJoinedPresheaf k X).obj (op ⦋0⦌)}
    (e : SSet.Edge x ((cosliceBoundaryRestriction k X f).app (op ⦋0⦌) b))
    (he : edgeIsInvertible X (e.map (boundaryProjection k X)).edge) :
    ∃ a : (simplexCoslice ⦋k⦌ X f).obj (op ⦋0⦌),
      (cosliceBoundaryRestriction k X f).app (op ⦋0⦌) a = x ∧
      ∃ g : SSet.Edge a b, (cosliceBoundaryRestriction k X f).app (op ⦋1⦌) g.edge = e.edge ∧
        edgeIsInvertible (simplexCoslice ⦋k⦌ X f) g.edge := by
  haveI := coslice_hasLiftingProperty hX k 0 0 (by decide) f
  haveI := coslice_hasLiftingProperty hX k 1 0 (by decide) f
  exact lift_invertible_edge_to_target (cosliceBoundaryRestriction k X f)
    (boundaryJoinedPresheaf_innerHornFillers hX k) b e
      (boundary_projection_reflects_invertible_edge hX k e he)

end

end DaggerOriginalAllPrefixBoundaryInvertibleLifting
