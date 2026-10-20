import OriginalLeftMappingTriangles

/-!
# Actual left-mapping-space components are the original homotopy-category Hom

Descent uses actual mapping-space edges, hence actual original left triangles.
Original edge representability gives surjectivity. The proved exact criterion
for equality in the native path quotient gives injectivity by constructing an
actual mapping-space edge. The conclusion uses the original native Hom set,
without substituting an auxiliary quotient or assuming the desired comparison.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalQuasicategoryLeftMappingSpace
open DaggerOriginalLeftMappingVertices DaggerOriginalLeftMappingTriangles
open DaggerOriginalQuasicategoryPathTriangleWitnesses

universe u

namespace DaggerOriginalLeftMappingPiZeroHom

noncomputable section

/-- An actual mapping-space edge identifies the original native Hom classes of its endpoints. -/
theorem vertexHomMk_eq_of_edge (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    {a b : (leftMappingSpace X x y).obj (op ⦋0⦌)}
    (e : SSet.Edge (X := leftMappingSpace X x y) a b) :
    vertexHomMk X x y a = vertexHomMk X x y b := by
  have h := SSet.Truncated.HomotopyCategory.homMk_comp_homMk (edgeTriangle X x y e)
  change SSet.Truncated.HomotopyCategory.homMk (vertexEdge X x y a) ≫
    SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (SSet.truncation 2).obj X) y) =
    SSet.Truncated.HomotopyCategory.homMk (vertexEdge X x y b) at h
  rw [SSet.Truncated.HomotopyCategory.homMk_id
    (V := (SSet.truncation 2).obj X) y, Category.comp_id] at h
  exact h

/-- The original native Hom class descends along the actual mapping-space component quotient. -/
def piZeroToHom (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) :
    (leftMappingSpace X x y).π₀ →
      (SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) x ⟶
        SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) y) :=
  Quot.lift (vertexHomMk X x y) (by
    rintro a b ⟨s, hs, ht⟩
    exact vertexHomMk_eq_of_edge X x y ⟨s, hs, ht⟩)

/-- On an actual vertex, the comparison is precisely its original native edge class. -/
theorem piZeroToHom_mk (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    (v : (leftMappingSpace X x y).obj (op ⦋0⦌)) :
    piZeroToHom X x y (SSet.π₀.mk v) = vertexHomMk X x y v := rfl

/-- Original path-quotient equality supplies equality of actual mapping-space components. -/
theorem piZeroToHom_injective {X : SSet.{u}} (hX : innerHornFillers X)
    (x y : X.obj (op ⦋0⦌)) : Function.Injective (piZeroToHom X x y) := by
  intro a b h
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨w, rfl⟩ := SSet.π₀.mk_surjective b
  rw [piZeroToHom_mk, piZeroToHom_mk] at h
  have hh := (original_homMk_eq_iff_leftHomotopic hX).mp h
  have hc := piZero_mk_eq_of_leftHomotopic X x y hh
  have hv : edgeVertex X x y (vertexEdge X x y v) = v :=
    (vertexEdgeEquiv X x y).symm_apply_apply v
  have hw : edgeVertex X x y (vertexEdge X x y w) = w :=
    (vertexEdgeEquiv X x y).symm_apply_apply w
  rw [hv, hw] at hc
  exact hc

/-- Every native original arrow is represented by a component of the actual left mapping space.
-/
theorem piZeroToHom_surjective {X : SSet.{u}} (hX : innerHornFillers X)
    (x y : X.obj (op ⦋0⦌)) : Function.Surjective (piZeroToHom X x y) := by
  intro f
  obtain ⟨v, hv⟩ := vertexHomMk_surjective hX x y f
  exact ⟨SSet.π₀.mk v, hv⟩

/-- The components of the actual standard left mapping space are the original native Hom set.
-/
def piZeroHomEquiv {X : SSet.{u}} (hX : innerHornFillers X) (x y : X.obj (op ⦋0⦌)) :
    (leftMappingSpace X x y).π₀ ≃
      (SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) x ⟶
        SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) y) :=
  Equiv.ofBijective (piZeroToHom X x y)
    ⟨piZeroToHom_injective hX x y, piZeroToHom_surjective hX x y⟩

/-- The same original component-to-Hom map is bijective for every inner-horn-filling input. -/
theorem piZeroToHom_bijective {X : SSet.{u}} (hX : innerHornFillers X)
    (x y : X.obj (op ⦋0⦌)) : Function.Bijective (piZeroToHom X x y) :=
  ⟨piZeroToHom_injective hX x y, piZeroToHom_surjective hX x y⟩

end

end DaggerOriginalLeftMappingPiZeroHom
