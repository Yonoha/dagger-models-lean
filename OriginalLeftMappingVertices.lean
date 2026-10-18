import OriginalQuasicategoryLeftMappingSpace
import OriginalQuasicategoryPathEdgeRepresentatives

/-!
# Actual vertices of the left mapping space and original edge representatives

The strict fiber vertices are exactly the actual edges with prescribed endpoints.
Their native homotopy-category classes cover the original Hom set for an
inner-horn-filling input. This is a statement about actual vertices and original
path classes; the descent to mapping-space components is proved separately.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryLeftMappingSpace
open DaggerOriginalQuasicategoryPathEdgeRepresentatives

universe u

namespace DaggerOriginalLeftMappingVertices

/-- The native left inclusion for two vertices is the original source coface. -/
theorem vertex_join_inl :
    AugmentedSimplexCategory.inl' ⦋0⦌ ⦋0⦌ = SimplexCategory.δ 1 := by decide

/-- The native right inclusion for two vertices is the original target coface. -/
theorem vertex_join_inr :
    AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌ = SimplexCategory.δ 0 := by decide

/-- A mapping-space vertex gives its original edge with exactly the fixed endpoints. -/
def vertexEdge (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    (v : (leftMappingSpace X x y).obj (op ⦋0⦌)) : SSet.Edge (X := X) x y where
  edge := v.val.val
  src_eq := by
    have h := v.val.property
    change X.map (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋0⦌).op v.val.val = x at h
    rw [vertex_join_inl] at h
    exact h
  tgt_eq := by
    have h := (SSet.Subcomplex.mem_fiber_obj_zero_iff
      (cosliceProjection ⦋0⦌ X x) y v.val).mp v.property
    change X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌).op v.val.val = y at h
    rw [vertex_join_inr] at h
    exact h

/-- An original edge with the fixed endpoints is an actual vertex of the strict fiber. -/
def edgeVertex (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) (e : SSet.Edge (X := X) x y) :
    (leftMappingSpace X x y).obj (op ⦋0⦌) := by
  let s : (simplexCoslice ⦋0⦌ X x).obj (op ⦋0⦌) := ⟨e.edge, by
    change X.map (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋0⦌).op e.edge = x
    rw [vertex_join_inl]
    exact e.src_eq⟩
  refine ⟨s, (SSet.Subcomplex.mem_fiber_obj_zero_iff _ _ _).mpr ?_⟩
  change X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌).op e.edge = y
  rw [vertex_join_inr]
  exact e.tgt_eq

/-- The vertex-edge correspondence is a literal equivalence, without any horn hypothesis. -/
def vertexEdgeEquiv (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) :
    (leftMappingSpace X x y).obj (op ⦋0⦌) ≃ SSet.Edge (X := X) x y where
  toFun := vertexEdge X x y
  invFun := edgeVertex X x y
  left_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := SSet.Edge.ext rfl

/-- The class of the actual original edge corresponding to a mapping-space vertex. -/
def vertexHomMk (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    (v : (leftMappingSpace X x y).obj (op ⦋0⦌)) :
    SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) x ⟶
      SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) y :=
  SSet.Truncated.HomotopyCategory.homMk (vertexEdge X x y v)

/-- Every original homotopy-category arrow is represented by an actual mapping-space vertex. -/
theorem vertexHomMk_surjective {X : SSet.{u}} (hX : innerHornFillers X)
    (x y : X.obj (op ⦋0⦌)) : Function.Surjective (vertexHomMk X x y) := by
  intro f
  obtain ⟨e, he⟩ := original_homMk_surjective X hX f
  refine ⟨edgeVertex X x y e, ?_⟩
  change SSet.Truncated.HomotopyCategory.homMk (vertexEdge X x y (edgeVertex X x y e)) = f
  have hv : vertexEdge X x y (edgeVertex X x y e) = e :=
    (vertexEdgeEquiv X x y).apply_symm_apply e
  rw [hv]
  exact he

end DaggerOriginalLeftMappingVertices
