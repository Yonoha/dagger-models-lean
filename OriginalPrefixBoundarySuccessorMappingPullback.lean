import OriginalPrefixBoundarySuccessorIsomorphisms

/-!
# Exact mapping pullback for the original successor prefix boundary

Transport the native two-piece pushout through the exact smaller-simplex and
smaller-boundary isomorphisms. Mapping that actual pushout into any X gives
the actual pullback of restriction functions. The entire original smaller
boundary, not merely its vertices, supplies the compatibility condition.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalPrefixBoundarySuccessorIsomorphisms

universe u

namespace DaggerOriginalPrefixBoundarySuccessorMappingPullback

noncomputable section

/-- The actual inclusion of the original smaller simplex into the original successor boundary.
-/
def firstFaceBoundaryInclusion (k n : ℕ) :
    (Δ[k + n + 1] : SSet.{u}) ⟶ prefixBoundary (k + 1) n :=
  (firstPrefixFaceIso k n).hom ≫ SSet.Subcomplex.homOfLE (firstPrefixFace_le_boundary k n)

/-- The original smaller-boundary inclusion and the remaining-face embedding form an actual
pushout, with the original successor boundary as target. -/
theorem successor_boundary_first_face_isPushout (k n : ℕ) :
    IsPushout (prefixBoundary.{u} k n).ι (boundaryToRest k n)
      (firstFaceBoundaryInclusion k n)
      (SSet.Subcomplex.homOfLE (restPrefixBoundary_le_boundary k n)) := by
  apply (successor_boundary_isPushout.{u} k n).of_iso'
    (successorOverlapIso k n) (firstPrefixFaceIso k n)
    (Iso.refl (restPrefixBoundary k n : SSet.{u}))
    (Iso.refl (prefixBoundary (k + 1) n : SSet.{u}))
  · exact successorOverlapIso_hom_comp_first k n
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Mapping the exact original successor boundary into any X gives the actual restriction
pullback over maps from the entire original smaller boundary. -/
theorem successor_boundary_maps_isPullback (X : SSet.{u}) (k n : ℕ) :
    IsPullback
      ((CategoryTheory.yoneda.obj X).map
        (SSet.Subcomplex.homOfLE (restPrefixBoundary_le_boundary k n)).op)
      ((CategoryTheory.yoneda.obj X).map (firstFaceBoundaryInclusion k n).op)
      ((CategoryTheory.yoneda.obj X).map (boundaryToRest k n).op)
      ((CategoryTheory.yoneda.obj X).map (prefixBoundary k n).ι.op) :=
  (successor_boundary_first_face_isPushout k n).op.map (CategoryTheory.yoneda.obj X)

/-- Compatible maps on the remaining faces and original smaller simplex glue to the exact
original successor boundary. -/
theorem successor_boundary_glue_first_face {X : SSet.{u}} (k n : ℕ)
    (a : (Δ[k + n + 1] : SSet.{u}) ⟶ X)
    (b : (restPrefixBoundary k n : SSet.{u}) ⟶ X)
    (w : (prefixBoundary k n).ι ≫ a = boundaryToRest k n ≫ b) :
    ∃ g : (prefixBoundary (k + 1) n : SSet.{u}) ⟶ X,
      firstFaceBoundaryInclusion k n ≫ g = a ∧
      SSet.Subcomplex.homOfLE (restPrefixBoundary_le_boundary k n) ≫ g = b := by
  let sq := successor_boundary_first_face_isPushout.{u} k n
  exact ⟨sq.desc a b w, sq.inl_desc a b w, sq.inr_desc a b w⟩

end

end DaggerOriginalPrefixBoundarySuccessorMappingPullback
