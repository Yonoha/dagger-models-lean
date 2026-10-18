import OriginalOuterTwoHornInverses
import OriginalOrdinaryCoreTwoHornFillers

/-!
# The same original core has a groupoid as its native homotopy category

The verified literal outer two-horn fillers are applied to the same core
subcomplex. Native path classes, including arbitrary composites, are invertible.
This is established before the unresolved higher outer horns; no candidate Kan
property or change to the original unit or homotopy category is made.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryInverseEdgeRepresentatives
open DaggerOriginalOuterTwoHornInverses
open DaggerOriginalOrdinaryCoreTwoHornFillers

universe u

namespace DaggerOriginalOrdinaryCorePathGroupoid

noncomputable section

/-- The literal right outer two-horn property of the same original core. -/
theorem core_rightOuterTwoHornFillers (X : SSet.{u}) (hX : innerHornFillers X) :
    rightOuterTwoHornFillers (ordinaryCoreCandidate X : SSet.{u}) :=
  core_outer22_filling X hX

/-- Every actual edge in the original core is invertible in that core's own native path quotient. -/
theorem core_homMk_isIso (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
  original_homMk_isIso (core_rightOuterTwoHornFillers X hX) e

/-- Arbitrary morphisms of the original core's own native path quotient are invertible. -/
theorem core_path_isIso (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : SSet.hoFunctor.obj (ordinaryCoreCandidate X : SSet.{u})} (f : x ⟶ y) : IsIso f :=
  original_path_isIso (core_rightOuterTwoHornFillers X hX) f

/-- Explicit groupoid structure on the same native homotopy category of the original core. -/
def corePathGroupoid (X : SSet.{u}) (hX : innerHornFillers X) :
    Groupoid (SSet.hoFunctor.obj (ordinaryCoreCandidate X : SSet.{u})) :=
  originalPathGroupoid (ordinaryCoreCandidate X : SSet.{u})
    (core_rightOuterTwoHornFillers X hX)

/-- Every actual core edge is invertible under that same core's own original unit. -/
theorem core_edge_isInvertible (X : SSet.{u}) (hX : innerHornFillers X)
    (e : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋1⦌)) :
    edgeIsInvertible (ordinaryCoreCandidate X : SSet.{u}) e := by
  exact (edgeIsInvertible_iff_original_homMk_isIso
    (ordinaryCoreCandidate X : SSet.{u}) (SSet.Edge.mk' e)).mpr
    (core_homMk_isIso X hX (SSet.Edge.mk' e))

/-- Taking the same original core again gives the top subcomplex, before assuming Kan. -/
theorem core_of_core_eq_top (X : SSet.{u}) (hX : innerHornFillers X) :
    ordinaryCoreCandidate (ordinaryCoreCandidate X : SSet.{u}) = ⊤ := by
  apply top_unique
  apply (le_ordinaryCoreCandidate_iff_edges_iso
    (ordinaryCoreCandidate X : SSet.{u}) ⊤).mpr
  intro e _
  exact core_edge_isInvertible X hX e

end

end DaggerOriginalOrdinaryCorePathGroupoid
