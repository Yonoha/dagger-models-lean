import OriginalPrefixDeleteFirstNativeJoin
import OriginalStandardCofaceIntersections

/-!
# The actual overlap in the successor prefix-boundary decomposition

The native first-prefix coface shifts omitted prefix vertices by one. The
preimage of the remaining-prefix union is exactly the original smaller
prefix boundary. Native image/preimage and exact range identities identify
the entire overlap, in all original dimensions and arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalPrefixDeleteFirstCoface
open DaggerOriginalStandardCofaceIntersections

universe u

namespace DaggerOriginalPrefixBoundarySuccessorOverlap

/-- The original smaller prefix vertex is exactly the preimage of the successor prefix vertex.
-/
theorem prefixDeleteFirst_eq_successorPrefix_iff (k n : ℕ)
    (s : Fin (k + n + 2)) (j : Fin (k + 1)) :
    (prefixDeleteFirstOperator k n).toOrderHom s = prefixIndex (k + 1) n j.succ ↔
      s = prefixIndex k n j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    rw [prefixDeleteFirstOperator_eval] at hv
    change s.val + 1 = j.val + 1 at hv
    change s.val = j.val
    omega
  · intro h
    subst s
    apply Fin.ext
    rw [prefixDeleteFirstOperator_eval]
    rfl

/-- The actual preimage of the other successor prefix faces is the original smaller boundary.
-/
theorem prefixDeleteFirst_preimage_rest (k n : ℕ) :
    (restPrefixBoundary.{u} k n).preimage (prefixDeleteFirstMap k n) =
      prefixBoundary k n := by
  ext q s
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      change (prefixDeleteFirstMap k n).app (op ⦋d⦌) s ∈
        (restPrefixBoundary k n).obj (op ⦋d⦌) ↔
        s ∈ (prefixBoundary k n).obj (op ⦋d⦌)
      simp only [restPrefixBoundary, prefixBoundary, Subfunctor.iSup_obj, Set.mem_iUnion]
      constructor
      · rintro ⟨j, hj⟩
        refine ⟨j, ?_⟩
        rw [SSet.stdSimplex.mem_face_iff] at hj ⊢
        simp only [Finset.mem_compl, Finset.mem_singleton] at hj ⊢
        intro a ha
        apply hj a
        change (prefixDeleteFirstOperator k n).toOrderHom
          (SSet.stdSimplex.asOrderHom s a) = prefixIndex (k + 1) n j.succ
        exact (prefixDeleteFirst_eq_successorPrefix_iff k n _ j).mpr ha
      · rintro ⟨j, hj⟩
        refine ⟨j, ?_⟩
        rw [SSet.stdSimplex.mem_face_iff] at hj ⊢
        simp only [Finset.mem_compl, Finset.mem_singleton] at hj ⊢
        intro a ha
        apply hj a
        exact (prefixDeleteFirst_eq_successorPrefix_iff k n
          (SSet.stdSimplex.asOrderHom s a) j).mp ha

/-- The entire overlap is the image of the exact original smaller boundary under that coface.
-/
theorem prefixDeleteFirst_boundary_image (k n : ℕ) :
    (prefixBoundary.{u} k n).image (prefixDeleteFirstMap k n) =
      restPrefixBoundary k n ⊓ firstPrefixFace k n := by
  have h := image_preimage_eq_inf_range (restPrefixBoundary.{u} k n)
    (prefixDeleteFirstMap k n)
  rw [prefixDeleteFirst_preimage_rest, prefixDeleteFirstMap_range] at h
  exact h

end DaggerOriginalPrefixBoundarySuccessorOverlap
