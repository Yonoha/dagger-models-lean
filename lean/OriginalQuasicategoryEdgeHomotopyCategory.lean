/-
The edge-quotient category arguments are adapted from the pinned Mathlib file
Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean.
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the original arguments: Julian Komaromy, Joël Riou
-/
import OriginalQuasicategoryEdgeHomotopies

/-!
# An auxiliary category of actual edge homotopy classes in arbitrary universe

This auxiliary category tests equations in the original path quotient via its
native lift constructor. It does not replace the original homotopy category,
unit, or core predicate. All composition triangles come from original inner horns.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open SSet.Edge.CompStruct
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryComposeEdges
open DaggerOriginalQuasicategoryTetrahedronFillers
open DaggerOriginalQuasicategoryEdgeHomotopies

universe u

namespace DaggerOriginalQuasicategoryEdgeHomotopyCategory

noncomputable section

/-- The actual left-homotopy setoid on original edges with these exact endpoints. -/
def edgeSetoid {X : SSet.{u}} (hX : innerHornFillers X)
    (x y : X.obj (op ⦋0⦌)) : Setoid (SSet.Edge x y) where
  r := leftHomotopic
  iseqv := ⟨left_refl, left_symm hX, left_trans hX⟩

/-- Choose an actual composite edge using a literal inner two-horn filler. -/
def composeEdge {X : SSet.{u}} (hX : innerHornFillers X)
    {x y z : X.obj (op ⦋0⦌)} (f : SSet.Edge x y) (g : SSet.Edge y z) : SSet.Edge x z :=
  (compose_edges hX f g).choose

/-- The chosen composite has an actual original composition triangle. -/
def compositionTriangle {X : SSet.{u}} (hX : innerHornFillers X)
    {x y z : X.obj (op ⦋0⦌)} (f : SSet.Edge x y) (g : SSet.Edge y z) :
    f.CompStruct g (composeEdge hX f g) := (compose_edges hX f g).choose_spec.some

/-- Original vertices, carrying the original inner-horn proof as a category parameter. -/
structure EdgeHomotopyCategory (X : SSet.{u}) (hX : innerHornFillers X) where
  ofVertex ::
  pt : X.obj (op ⦋0⦌)

namespace EdgeHomotopyCategory

variable {X : SSet.{u}} (hX : innerHornFillers X)

/-- Actual edges modulo their original left homotopy triangles. -/
def Hom (x y : EdgeHomotopyCategory X hX) := Quotient (edgeSetoid hX x.pt y.pt)

instance : CategoryStruct (EdgeHomotopyCategory X hX) where
  Hom := Hom hX
  id x := Quotient.mk (edgeSetoid hX x.pt x.pt) (SSet.Edge.id x.pt)
  comp {x y z} := Quotient.lift₂
    (s₁ := edgeSetoid hX x.pt y.pt) (s₂ := edgeSetoid hX y.pt z.pt)
    (fun f g ↦ Quotient.mk (edgeSetoid hX x.pt z.pt) (composeEdge hX f g))
    (fun _ _ _ _ hf hg ↦ Quotient.sound
      (composition_unique hX (compositionTriangle hX _ _) (compositionTriangle hX _ _) hf hg))

/-- The original vertex regarded as an object of the auxiliary category. -/
def mk (x : X.obj (op ⦋0⦌)) : EdgeHomotopyCategory X hX := ⟨x⟩

/-- The auxiliary class of an actual original edge. -/
def homMk {x y : X.obj (op ⦋0⦌)} (f : SSet.Edge x y) : mk hX x ⟶ mk hX y :=
  Quotient.mk (edgeSetoid hX x y) f

/-- Actual left-homotopic edges have the same auxiliary class. -/
theorem homMk_eq_of_leftHomotopic {x y : X.obj (op ⦋0⦌)} {f g : SSet.Edge x y}
    (h : leftHomotopic f g) : homMk hX f = homMk hX g := Quotient.sound h

/-- The native constant edge represents the auxiliary identity. -/
theorem homMk_id (x : X.obj (op ⦋0⦌)) : homMk hX (SSet.Edge.id x) = 𝟙 (mk hX x) := rfl

/-- An actual original triangle proves the corresponding auxiliary composition equation. -/
theorem homMk_comp {x y z : X.obj (op ⦋0⦌)}
    {f : SSet.Edge x y} {g : SSet.Edge y z} {h : SSet.Edge x z}
    (s : f.CompStruct g h) : homMk hX f ≫ homMk hX g = homMk hX h :=
  homMk_eq_of_leftHomotopic hX
    (composition_unique hX (compositionTriangle hX f g) s (left_refl f) (left_refl g))

instance : Category (EdgeHomotopyCategory X hX) where
  id_comp := by
    rintro _ _ ⟨f⟩
    exact homMk_eq_of_leftHomotopic hX
      (composition_unique hX (compositionTriangle hX _ f) (idComp f)
        (left_refl _) (left_refl f))
  comp_id := by
    rintro _ _ ⟨f⟩
    exact homMk_eq_of_leftHomotopic hX
      (composition_unique hX (compositionTriangle hX f _) (compId f)
        (left_refl f) (left_refl _))
  assoc := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact homMk_comp hX ((fill31 hX (compositionTriangle hX f g)
      (compositionTriangle hX g h) (compositionTriangle hX _ _)).some)

/-- Equality of auxiliary classes is exactly the original left triangle homotopy condition. -/
theorem homMk_eq_iff_leftHomotopic {x y : X.obj (op ⦋0⦌)} {f g : SSet.Edge x y} :
    homMk hX f = homMk hX g ↔ leftHomotopic f g := Quotient.eq_iff_equiv

end EdgeHomotopyCategory

end

end DaggerOriginalQuasicategoryEdgeHomotopyCategory
