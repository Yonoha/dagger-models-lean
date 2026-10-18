import OriginalPrefixBoundaryConeOperators

/-!
# The exact native cone unit on the original smaller prefix boundary

Prepending preserves the missing original prefix vertex, hence lands in the
remaining successor prefix boundary. This defines a natural simplicial map
into its vertex-join presheaf. Its original suffix restriction is exactly
the retained boundary-to-rest map from the successor pushout.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedCofaces
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalPrefixBoundarySuccessorIsomorphisms
open DaggerOriginalPrefixBoundaryConeOperators

universe u

namespace DaggerOriginalPrefixBoundaryConeUnit

/-- Prepending retains the same missing original prefix vertex, shifted by one. -/
theorem prefixCone_mem_rest (k n : ℕ) {d : SimplexCategory}
    (α : d ⟶ ⦋k + n + 1⦌)
    (hα : SSet.stdSimplex.objEquiv.{u}.symm α ∈ (prefixBoundary k n).obj (op d)) :
    SSet.stdSimplex.objEquiv.{u}.symm (prefixConeOperator k n α) ∈
      (restPrefixBoundary.{u} k n).obj (op ((ordinalJoinLeft ⦋0⦌).obj d)) := by
  induction d using SimplexCategory.rec with | h d =>
    simp only [prefixBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hα
    obtain ⟨j, hj⟩ := hα
    simp only [restPrefixBoundary, Subfunctor.iSup_obj, Set.mem_iUnion]
    refine ⟨j, ?_⟩
    change SSet.stdSimplex.objEquiv.{u}.symm (prefixConeOperator k n α) ∈
      (SSet.stdSimplex.face.{u} {prefixIndex (k + 1) n j.succ}ᶜ).obj (op ⦋0 + d + 1⦌)
    rw [SSet.stdSimplex.mem_face_iff] at hj ⊢
    simp only [Finset.mem_compl, Finset.mem_singleton] at hj ⊢
    intro a ha
    change (prefixConeOperator k n α).toOrderHom a = prefixIndex (k + 1) n j.succ at ha
    have hv := congrArg Fin.val ha
    rcases vertex_eq_prefix_or_suffix 0 d a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [prefixIndex_eq_native, prefixConeOperator_prefix_eval] at hv
      change 0 = j.val + 1 at hv
      omega
    · rw [suffixIndex_eq_native, prefixConeOperator_suffix_eval] at hv
      apply hj b
      change α.toOrderHom b = prefixIndex k n j
      apply Fin.ext
      change (α.toOrderHom b).val = j.val
      change (α.toOrderHom b).val + 1 = j.val + 1 at hv
      omega

/-- The original boundary simplex with its actual native cone and missing-vertex certificate. -/
def prefixConeBoundarySimplex (k n : ℕ) {d : SimplexCategory}
    (s : (prefixBoundary k n : SSet.{u}).obj (op d)) :
    (restPrefixBoundary k n : SSet.{u}).obj (op ((ordinalJoinLeft ⦋0⦌).obj d)) :=
  ⟨SSet.stdSimplex.objEquiv.symm (prefixConeOperator k n (SSet.stdSimplex.objEquiv s.val)),
    prefixCone_mem_rest k n _ (by simpa only [Equiv.symm_apply_apply] using s.property)⟩

/-- The cone construction is a map of the actual original simplicial sets. -/
def prefixConeBoundaryUnit (k n : ℕ) :
    (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ (restPrefixBoundary k n) where
  app q s := prefixConeBoundarySimplex k n s
  naturality a b β := by
    funext s
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    change prefixConeOperator k n (β.unop ≫ SSet.stdSimplex.objEquiv s.val) =
      (ordinalJoinLeft ⦋0⦌).map β.unop ≫
        prefixConeOperator k n (SSet.stdSimplex.objEquiv s.val)
    exact prefixConeOperator_precomp k n β.unop _

/-- Evaluation on the original right block recovers the same retained boundary embedding. -/
theorem prefixConeBoundaryUnit_comp_suffix (k n : ℕ) :
    prefixConeBoundaryUnit.{u} k n ≫ suffixProjection ⦋0⦌ (restPrefixBoundary k n) =
      boundaryToRest k n := by
  apply (cancel_mono (restPrefixBoundary k n).ι).mp
  rw [Category.assoc, boundaryToRest_comp_inclusion]
  ext q s
  apply SSet.stdSimplex.objEquiv.injective
  change AugmentedSimplexCategory.inr' ⦋0⦌ q.unop ≫
      prefixConeOperator k n (SSet.stdSimplex.objEquiv s.val) =
    SSet.stdSimplex.objEquiv s.val ≫
      DaggerOriginalPrefixDeleteFirstCoface.prefixDeleteFirstOperator k n
  exact prefixConeOperator_suffix_comp k n _

end DaggerOriginalPrefixBoundaryConeUnit
