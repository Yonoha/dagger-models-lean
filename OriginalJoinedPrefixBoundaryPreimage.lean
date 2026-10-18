import OriginalJoinedBoundaryRestriction

/-!
# Exact pullback of the joined prefix boundary

Every native ordinal-sum operator has exactly the same preimage of a prefix
boundary. This equality identifies the overlap used when gluing a prescribed
boundary map and the faces supplied by the original coslice horn.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaces
open DaggerOriginalJoinedPrefixBoundaryFunctor

universe u

namespace DaggerOriginalJoinedPrefixBoundaryPreimage

/-- Prefix-boundary membership is reflected as well as preserved by every joined operator. -/
theorem prefixBoundary_map_mem_iff (k : ℕ) {m n : SimplexCategory}
    {q : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (s : (Δ[k + m.len + 1] : SSet.{u}).obj q) :
    (SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map α)).app q s ∈
      (prefixBoundary k n.len).obj q ↔ s ∈ (prefixBoundary k m.len).obj q := by
  constructor
  · induction m using SimplexCategory.rec with | h m =>
      induction n using SimplexCategory.rec with | h n =>
        induction q using Opposite.rec with | op q =>
          induction q using SimplexCategory.rec with | h d =>
            intro hs
            simp only [prefixBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hs ⊢
            obtain ⟨j, hj⟩ := hs
            refine ⟨j, ?_⟩
            rw [SSet.stdSimplex.mem_face_iff] at hj ⊢
            simp only [Finset.mem_compl, Finset.mem_singleton] at hj ⊢
            intro a ha
            apply hj a
            change ((ordinalJoinLeft ⦋k⦌).map α).toOrderHom
              (SSet.stdSimplex.asOrderHom s a) = prefixIndex k n j
            exact (joinMap_eq_prefix_iff k α (SSet.stdSimplex.asOrderHom s a) j).mpr ha
  · exact prefixBoundary_map_mem k α s

/-- The literal inverse image of the boundary is the literal boundary in the source. -/
theorem prefixBoundary_preimage (k : ℕ) {m n : SimplexCategory} (α : m ⟶ n) :
    (prefixBoundary.{u} k n.len).preimage
      (SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map α)) = prefixBoundary k m.len := by
  ext q s
  exact prefixBoundary_map_mem_iff k α s

/-- The overlap with a joined coface is exactly the image of the original smaller boundary. -/
theorem prefixBoundary_image_coface (k n : ℕ) (i : Fin (n + 2)) :
    (prefixBoundary.{u} k n).image
      (SSet.stdSimplex.δ (suffixIndex k (n + 1) i)) =
      prefixBoundary k (n + 1) ⊓ SSet.stdSimplex.face {suffixIndex k (n + 1) i}ᶜ := by
  have hpre := prefixBoundary_preimage.{u} k (SimplexCategory.δ i)
  rw [joinMap_coface] at hpre
  change (prefixBoundary.{u} k (n + 1)).preimage
    (SSet.stdSimplex.δ (suffixIndex k (n + 1) i)) = prefixBoundary k n at hpre
  apply le_antisymm
  · apply le_inf
    · rw [SSet.Subcomplex.image_le_iff, hpre]
    · simpa only [SSet.stdSimplex.range_δ] using
        (SSet.Subcomplex.image_le_range (prefixBoundary.{u} k n)
          (SSet.stdSimplex.δ (suffixIndex k (n + 1) i)))
  · intro q s hs
    obtain ⟨t, ht⟩ := (show s ∈ (SSet.Subcomplex.range
      (SSet.stdSimplex.δ (suffixIndex k (n + 1) i))).obj q by
        simpa only [SSet.stdSimplex.range_δ] using hs.2)
    refine ⟨t, ?_, ht⟩
    rw [← hpre]
    change (SSet.stdSimplex.δ (suffixIndex k (n + 1) i)).app q t ∈
      (prefixBoundary k (n + 1)).obj q
    rw [ht]
    exact hs.1

end DaggerOriginalJoinedPrefixBoundaryPreimage
