import OriginalJoinedPrefixBoundaryPreimage

/-!
# Exact two-piece decomposition of every original successor prefix boundary

Split the original omitted-prefix faces into the first omitted vertex and
all the remaining omitted vertices. The native lattice bicartesian square
is an actual simplicial pushout, giving exact gluing and uniqueness on the
original successor boundary. All original prefix and suffix dimensions remain.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalJoinedHornGeometry

universe u

namespace DaggerOriginalPrefixBoundarySuccessorShapes

/-- The actual first omitted-prefix face in the original successor boundary. -/
def firstPrefixFace (k n : ℕ) : (Δ[k + 1 + n + 1] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face {prefixIndex (k + 1) n 0}ᶜ

/-- The actual union of all the other omitted-prefix faces in that same ambient simplex. -/
def restPrefixBoundary (k n : ℕ) : (Δ[k + 1 + n + 1] : SSet.{u}).Subcomplex :=
  ⨆ j : Fin (k + 1), SSet.stdSimplex.face {prefixIndex (k + 1) n j.succ}ᶜ

/-- The first omitted vertex is the actual zero vertex of the original ambient ordinal. -/
theorem firstPrefixIndex_eq_zero (k n : ℕ) :
    prefixIndex (k + 1) n 0 = 0 := Fin.ext rfl

/-- The two actual subcomplexes have union exactly the original successor prefix boundary. -/
theorem prefixBoundary_successor_decomposition (k n : ℕ) :
    prefixBoundary.{u} (k + 1) n = firstPrefixFace k n ⊔ restPrefixBoundary k n := by
  apply le_antisymm
  · rw [prefixBoundary, iSup_le_iff]
    intro j
    refine Fin.cases ?_ (fun a ↦ ?_) j
    · exact le_sup_left
    · exact (le_iSup (fun a : Fin (k + 1) ↦
        SSet.stdSimplex.face {prefixIndex (k + 1) n a.succ}ᶜ) a).trans le_sup_right
  · apply sup_le
    · exact le_iSup (fun j : Fin (k + 2) ↦
        SSet.stdSimplex.face {prefixIndex (k + 1) n j}ᶜ) 0
    · rw [restPrefixBoundary, iSup_le_iff]
      intro j
      exact le_iSup (fun a : Fin (k + 2) ↦
        SSet.stdSimplex.face {prefixIndex (k + 1) n a}ᶜ) j.succ

/-- The first actual face enters the same original successor boundary. -/
theorem firstPrefixFace_le_boundary (k n : ℕ) :
    firstPrefixFace.{u} k n ≤ prefixBoundary (k + 1) n := by
  rw [prefixBoundary_successor_decomposition]
  exact le_sup_left

/-- The remaining actual prefix faces enter the same original successor boundary. -/
theorem restPrefixBoundary_le_boundary (k n : ℕ) :
    restPrefixBoundary.{u} k n ≤ prefixBoundary (k + 1) n := by
  rw [prefixBoundary_successor_decomposition]
  exact le_sup_right

/-- The exact original face inclusions form a native simplicial pushout. -/
theorem successor_boundary_isPushout (k n : ℕ) :
    IsPushout
      (SSet.Subcomplex.homOfLE (inf_le_left :
        firstPrefixFace.{u} k n ⊓ restPrefixBoundary k n ≤ firstPrefixFace k n))
      (SSet.Subcomplex.homOfLE (inf_le_right :
        firstPrefixFace.{u} k n ⊓ restPrefixBoundary k n ≤ restPrefixBoundary k n))
      (SSet.Subcomplex.homOfLE (firstPrefixFace_le_boundary k n))
      (SSet.Subcomplex.homOfLE (restPrefixBoundary_le_boundary k n)) := by
  have sq : SSet.Subcomplex.BicartSq (firstPrefixFace.{u} k n ⊓ restPrefixBoundary k n)
      (firstPrefixFace k n) (restPrefixBoundary k n) (prefixBoundary (k + 1) n) :=
    ⟨(prefixBoundary_successor_decomposition k n).symm, rfl⟩
  exact sq.isPushout

/-- Maps agreeing on the entire original overlap glue to the exact successor boundary. -/
theorem successor_boundary_glue {X : SSet.{u}} (k n : ℕ)
    (a : (firstPrefixFace k n : SSet.{u}) ⟶ X)
    (b : (restPrefixBoundary k n : SSet.{u}) ⟶ X)
    (w : SSet.Subcomplex.homOfLE inf_le_left ≫ a =
      SSet.Subcomplex.homOfLE inf_le_right ≫ b) :
    ∃ g : (prefixBoundary (k + 1) n : SSet.{u}) ⟶ X,
      SSet.Subcomplex.homOfLE (firstPrefixFace_le_boundary k n) ≫ g = a ∧
      SSet.Subcomplex.homOfLE (restPrefixBoundary_le_boundary k n) ≫ g = b := by
  let sq := successor_boundary_isPushout.{u} k n
  exact ⟨sq.desc a b w, sq.inl_desc a b w, sq.inr_desc a b w⟩

/-- A map on the same original boundary is determined by both actual pieces. -/
theorem successor_boundary_hom_ext {X : SSet.{u}} (k n : ℕ)
    (a b : (prefixBoundary (k + 1) n : SSet.{u}) ⟶ X)
    (hfirst : SSet.Subcomplex.homOfLE (firstPrefixFace_le_boundary k n) ≫ a =
      SSet.Subcomplex.homOfLE (firstPrefixFace_le_boundary k n) ≫ b)
    (hrest : SSet.Subcomplex.homOfLE (restPrefixBoundary_le_boundary k n) ≫ a =
      SSet.Subcomplex.homOfLE (restPrefixBoundary_le_boundary k n) ≫ b) : a = b :=
  (successor_boundary_isPushout k n).hom_ext hfirst hrest

end DaggerOriginalPrefixBoundarySuccessorShapes
