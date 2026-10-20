/-
The homotopy arguments are adapted from the pinned Mathlib file
Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean.
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the original arguments: Julian Komaromy, Joël Riou
-/
import OriginalQuasicategoryTetrahedronFillers

/-!
# Actual edge homotopies from original inner horns in arbitrary universe

Use the same left and right composition-triangle conditions as pinned Mathlib.
The actual inner tetrahedron fillers supply the equivalence and composition
arguments directly for the original simplicial set. The original path quotient
and its unit are unchanged.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open SSet.Edge.CompStruct
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryTetrahedronFillers

universe u

namespace DaggerOriginalQuasicategoryEdgeHomotopies

/-- Left homotopy is an actual triangle whose second short edge is the constant edge. -/
def leftHomotopic {X : SSet.{u}} {x y : X.obj (op ⦋0⦌)} (f g : SSet.Edge x y) : Prop :=
  Nonempty (f.CompStruct (SSet.Edge.id y) g)

/-- Right homotopy is an actual triangle whose first short edge is the constant edge. -/
def rightHomotopic {X : SSet.{u}} {x y : X.obj (op ⦋0⦌)} (f g : SSet.Edge x y) : Prop :=
  Nonempty ((SSet.Edge.id x).CompStruct f g)

/-- The native constant-side triangle witnesses reflexive left homotopy. -/
theorem left_refl {X : SSet.{u}} {x y : X.obj (op ⦋0⦌)} (f : SSet.Edge x y) :
    leftHomotopic f f := ⟨compId f⟩

/-- The native constant-side triangle witnesses reflexive right homotopy. -/
theorem right_refl {X : SSet.{u}} {x y : X.obj (op ⦋0⦌)} (f : SSet.Edge x y) :
    rightHomotopic f f := ⟨idComp f⟩

/-- Original inner (3,1)-horn filling makes actual left homotopy symmetric. -/
theorem left_symm {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} {f g : SSet.Edge x y} (h : leftHomotopic f g) :
    leftHomotopic g f := by
  obtain ⟨h⟩ := h
  exact fill31 hX h (idComp (SSet.Edge.id y)) (compId f)

/-- Original inner (3,2)-horn filling makes actual left homotopy transitive. -/
theorem left_trans {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} {f g k : SSet.Edge x y}
    (hfg : leftHomotopic f g) (hgk : leftHomotopic g k) : leftHomotopic f k := by
  obtain ⟨hfg⟩ := hfg
  obtain ⟨hgk⟩ := hgk
  exact fill32 hX hfg (idComp (SSet.Edge.id y)) hgk

/-- Original inner (3,2)-horn filling makes actual right homotopy symmetric. -/
theorem right_symm {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} {f g : SSet.Edge x y} (h : rightHomotopic f g) :
    rightHomotopic g f := by
  obtain ⟨h⟩ := h
  exact fill32 hX (idComp (SSet.Edge.id x)) h (idComp f)

/-- Original inner (3,1)-horn filling makes actual right homotopy transitive. -/
theorem right_trans {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} {f g k : SSet.Edge x y}
    (hfg : rightHomotopic f g) (hgk : rightHomotopic g k) : rightHomotopic f k := by
  obtain ⟨hfg⟩ := hfg
  obtain ⟨hgk⟩ := hgk
  exact fill31 hX (idComp (SSet.Edge.id x)) hfg hgk

/-- Original inner (3,2)-horn filling changes a left triangle to a right triangle. -/
theorem left_to_right {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} {f g : SSet.Edge x y} (h : leftHomotopic f g) :
    rightHomotopic f g := by
  obtain ⟨h⟩ := h
  exact fill32 hX (idComp f) (compId f) h

/-- Original inner (3,1)-horn filling changes a right triangle to a left triangle. -/
theorem right_to_left {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} {f g : SSet.Edge x y} (h : rightHomotopic f g) :
    leftHomotopic f g := by
  obtain ⟨h⟩ := h
  exact fill31 hX (idComp f) (compId f) h

/-- The two original triangle homotopy conditions coincide under the actual inner-horn premise. -/
theorem left_iff_right {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} {f g : SSet.Edge x y} :
    leftHomotopic f g ↔ rightHomotopic f g := ⟨left_to_right hX, right_to_left hX⟩

/-- Original composition triangles respect homotopies in both of their short edges. -/
theorem composition_unique {X : SSet.{u}} (hX : innerHornFillers X)
    {x y z : X.obj (op ⦋0⦌)}
    {f f' : SSet.Edge x y} {g g' : SSet.Edge y z} {h h' : SSet.Edge x z}
    (s : f.CompStruct g h) (s' : f'.CompStruct g' h')
    (hf : leftHomotopic f f') (hg : leftHomotopic g g') : leftHomotopic h h' := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := left_to_right hX hg
  obtain ⟨s₁⟩ := fill32 hX hf (idComp g') s'
  obtain ⟨s₂⟩ := fill31 hX (compId f) hg s₁
  exact fill31 hX s (compId g) s₂

end DaggerOriginalQuasicategoryEdgeHomotopies
