import OriginalLeftMappingVertices
import OriginalQuasicategoryPathTriangleWitnesses
import TopCatModelCategory.SSet.PiZero

/-!
# Actual mapping-space edges are original left homotopy triangles

Both constructions retain the original two-simplex. The strict fiber condition
is exactly that its suffix edge is the original identity at y. Its two endpoint
faces are the prescribed original edges. Consequently such a triangle supplies
an actual edge joining their vertices in the same left mapping space.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalLeftMappingVertices

universe u

namespace DaggerOriginalLeftMappingTriangles

/-- The joined source operator selects the original 01 edge of the triangle. -/
theorem joined_source_coface :
    (ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (n := 0) 1) =
      SimplexCategory.δ (n := 1) 2 := by decide

/-- The joined target operator selects the original 02 edge of the triangle. -/
theorem joined_target_coface :
    (ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (n := 0) 0) =
      SimplexCategory.δ (n := 1) 1 := by decide

/-- The triangle suffix is its actual 12 edge. -/
theorem triangle_suffix :
    AugmentedSimplexCategory.inr' ⦋0⦌ ⦋1⦌ = SimplexCategory.δ 0 := by decide

/-- The triangle prefix selects the original initial vertex through the 01 edge. -/
theorem triangle_prefix :
    AugmentedSimplexCategory.inl' ⦋0⦌ ⦋1⦌ =
      SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.δ (n := 1) 2 := by decide

/-- The literal constant one-simplex is the native identity degeneracy. -/
theorem constant_one_operator :
    (⦋1⦌ : SimplexCategory).const ⦋0⦌ 0 = SimplexCategory.σ 0 := by decide

/-- An actual mapping-space edge gives the same original left-homotopy triangle. -/
def edgeTriangle (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    {a b : (leftMappingSpace X x y).obj (op ⦋0⦌)}
    (e : SSet.Edge (X := leftMappingSpace X x y) a b) :
    (vertexEdge X x y a).CompStruct (SSet.Edge.id y) (vertexEdge X x y b) where
  simplex := e.edge.val.val
  d₂ := by
    have h := congrArg (fun v ↦ v.val.val) e.src_eq
    change X.map ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (n := 0) 1)).op e.edge.val.val =
      a.val.val at h
    rw [joined_source_coface] at h
    exact h
  d₀ := by
    have h := (SSet.Subcomplex.mem_fiber_obj_iff
      (cosliceProjection ⦋0⦌ X x) y e.edge.val).mp e.edge.property
    change X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋1⦌).op e.edge.val.val =
      X.map ((⦋1⦌ : SimplexCategory).const ⦋0⦌ 0).op y at h
    rw [triangle_suffix, constant_one_operator] at h
    exact h
  d₁ := by
    have h := congrArg (fun v ↦ v.val.val) e.tgt_eq
    change X.map ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (n := 0) 0)).op e.edge.val.val =
      b.val.val at h
    rw [joined_target_coface] at h
    exact h

/-- An original left triangle supplies an actual one-simplex of the strict mapping-space fiber.
-/
def triangleSimplex (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    {f g : SSet.Edge (X := X) x y} (t : f.CompStruct (SSet.Edge.id y) g) :
    (leftMappingSpace X x y).obj (op ⦋1⦌) := by
  let s : (simplexCoslice ⦋0⦌ X x).obj (op ⦋1⦌) := ⟨t.simplex, by
    change X.map (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋1⦌).op t.simplex = x
    rw [triangle_prefix, op_comp, X.map_comp]
    change X.δ 1 (X.δ 2 t.simplex) = x
    rw [t.d₂, f.src_eq]⟩
  refine ⟨s, (SSet.Subcomplex.mem_fiber_obj_iff _ _ _).mpr ?_⟩
  change X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋1⦌).op t.simplex =
    X.map ((⦋1⦌ : SimplexCategory).const ⦋0⦌ 0).op y
  rw [triangle_suffix, constant_one_operator]
  exact t.d₀

/-- The same triangle gives an actual mapping-space edge with the exact edge vertices. -/
def triangleEdge (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    {f g : SSet.Edge (X := X) x y} (t : f.CompStruct (SSet.Edge.id y) g) :
    SSet.Edge (X := leftMappingSpace X x y) (edgeVertex X x y f) (edgeVertex X x y g) where
  edge := triangleSimplex X x y t
  src_eq := by
    apply Subtype.ext
    apply Subtype.ext
    change X.map ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (n := 0) 1)).op t.simplex = f.edge
    rw [joined_source_coface]
    exact t.d₂
  tgt_eq := by
    apply Subtype.ext
    apply Subtype.ext
    change X.map ((ordinalJoinLeft ⦋0⦌).map (SimplexCategory.δ (n := 0) 0)).op t.simplex = g.edge
    rw [joined_target_coface]
    exact t.d₁

/-- Original left homotopy implies equality of actual mapping-space components. -/
theorem piZero_mk_eq_of_leftHomotopic (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    {f g : SSet.Edge (X := X) x y}
    (h : DaggerOriginalQuasicategoryEdgeHomotopies.leftHomotopic f g) :
    SSet.π₀.mk (edgeVertex X x y f) = SSet.π₀.mk (edgeVertex X x y g) := by
  obtain ⟨t⟩ := h
  let e := triangleEdge X x y t
  exact SSet.π₀.sound e.edge e.src_eq e.tgt_eq

end DaggerOriginalLeftMappingTriangles
