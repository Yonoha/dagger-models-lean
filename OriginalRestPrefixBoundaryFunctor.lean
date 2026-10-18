import OriginalPrefixBoundaryConeUnit

/-!
# Original remaining successor prefix boundaries and their native operators

The original successor join maps preserve each missing successor prefix vertex.
Native subcomplex lifts give the actual cosimplicial remaining-boundary object,
with exact ambient maps. No change of dimension or filling assumption is made.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaces DaggerOriginalPrefixBoundarySuccessorShapes

universe u

namespace DaggerOriginalRestPrefixBoundaryFunctor

/-- All native original suffix operators preserve the same remaining-prefix predicate. -/
theorem restPrefixBoundary_map_mem (k : ℕ) {m n : SimplexCategory}
    {q : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (s : (Δ[k + 1 + m.len + 1] : SSet.{u}).obj q)
    (hs : s ∈ (restPrefixBoundary k m.len).obj q) :
    (SSet.stdSimplex.map ((ordinalJoinLeft ⦋k + 1⦌).map α)).app q s ∈
      (restPrefixBoundary k n.len).obj q := by
  induction m using SimplexCategory.rec with | h m =>
    induction n using SimplexCategory.rec with | h n =>
      induction q using Opposite.rec with | op q =>
        induction q using SimplexCategory.rec with | h d =>
          simp only [restPrefixBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hs ⊢
          obtain ⟨j, hj⟩ := hs
          refine ⟨j, ?_⟩
          rw [SSet.stdSimplex.mem_face_iff] at hj ⊢
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj ⊢
          intro a ha
          apply hj a
          change ((ordinalJoinLeft ⦋k + 1⦌).map α).toOrderHom
            (SSet.stdSimplex.asOrderHom s a) = prefixIndex (k + 1) n j.succ at ha
          exact (joinMap_eq_prefix_iff (k + 1) α _ j.succ).mp ha

/-- The native successor join map on the actual remaining prefix boundary. -/
def restPrefixBoundaryMap (k : ℕ) {m n : SimplexCategory} (α : m ⟶ n) :
    (restPrefixBoundary k m.len : SSet.{u}) ⟶ (restPrefixBoundary k n.len : SSet.{u}) :=
  SSet.Subcomplex.lift ((restPrefixBoundary k m.len).ι ≫
    SSet.stdSimplex.map ((ordinalJoinLeft ⦋k + 1⦌).map α)) (by
      intro q s hs
      obtain ⟨t, rfl⟩ := hs
      exact restPrefixBoundary_map_mem k α t.val t.property)

/-- The exact ambient operator is retained after inclusion. -/
theorem restPrefixBoundaryMap_comp_inclusion (k : ℕ) {m n : SimplexCategory}
    (α : m ⟶ n) :
    restPrefixBoundaryMap.{u} k α ≫ (restPrefixBoundary k n.len).ι =
      (restPrefixBoundary k m.len).ι ≫
        SSet.stdSimplex.map ((ordinalJoinLeft ⦋k + 1⦌).map α) :=
  SSet.Subcomplex.lift_ι _ _

/-- Every original suffix operator acts on the original remaining-boundary shapes. -/
def restPrefixBoundaryFunctor (k : ℕ) : SimplexCategory ⥤ SSet.{u} where
  obj n := (restPrefixBoundary k n.len : SSet.{u})
  map α := restPrefixBoundaryMap k α
  map_id n := by
    apply (cancel_mono (restPrefixBoundary k n.len).ι).mp
    rw [restPrefixBoundaryMap_comp_inclusion]
    rw [(ordinalJoinLeft ⦋k + 1⦌).map_id n,
      CategoryTheory.Functor.map_id SSet.stdSimplex ((ordinalJoinLeft ⦋k + 1⦌).obj n)]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  map_comp {a b c} α β := by
    apply (cancel_mono (restPrefixBoundary k c.len).ι).mp
    rw [restPrefixBoundaryMap_comp_inclusion, Category.assoc,
      restPrefixBoundaryMap_comp_inclusion, ← Category.assoc,
      restPrefixBoundaryMap_comp_inclusion]
    simp only [Functor.map_comp, Category.assoc]

end DaggerOriginalRestPrefixBoundaryFunctor
