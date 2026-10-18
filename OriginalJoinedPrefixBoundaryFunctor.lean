import OriginalJoinedCofaces

/-!
# Actual joined prefix boundaries as a cosimplicial object

The boundary-and-right-simplex shape is the union of the original faces
omitting a left-block vertex. Native ordinal-sum maps preserve this union:
a missing left-block vertex cannot enter the image from the right block.
The existing native subcomplex lift then supplies the exact maps, inclusion
diagrams, identities and compositions in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaces

universe u

namespace DaggerOriginalJoinedPrefixBoundaryFunctor

noncomputable section

/-- Every native joined simplex operator preserves the original prefix-boundary predicate. -/
theorem prefixBoundary_map_mem (k : ℕ) {m n : SimplexCategory}
    {q : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (s : (Δ[k + m.len + 1] : SSet.{u}).obj q)
    (hs : s ∈ (prefixBoundary k m.len).obj q) :
    (SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map α)).app q s ∈
      (prefixBoundary k n.len).obj q := by
  induction m using SimplexCategory.rec with | h m =>
    induction n using SimplexCategory.rec with | h n =>
      induction q using Opposite.rec with | op q =>
        induction q using SimplexCategory.rec with | h d =>
          simp only [prefixBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hs ⊢
          obtain ⟨j, hj⟩ := hs
          refine ⟨j, ?_⟩
          rw [SSet.stdSimplex.mem_face_iff] at hj ⊢
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj ⊢
          intro a
          change ((ordinalJoinLeft ⦋k⦌).map α).toOrderHom
            (SSet.stdSimplex.asOrderHom s a) ≠ prefixIndex k n j
          intro h
          have hv := (joinMap_eq_prefix_iff k α (SSet.stdSimplex.asOrderHom s a) j).mp h
          exact hj a hv

/-- The actual native ordinal-sum map lifts between the actual joined prefix boundaries. -/
def prefixBoundaryMap (k : ℕ) {m n : SimplexCategory} (α : m ⟶ n) :
    (prefixBoundary k m.len : SSet.{u}) ⟶ (prefixBoundary k n.len : SSet.{u}) :=
  SSet.Subcomplex.lift ((prefixBoundary k m.len).ι ≫
    SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map α)) (by
      intro q s hs
      obtain ⟨t, rfl⟩ := hs
      exact prefixBoundary_map_mem k α t.val t.property)

/-- The lifted map followed by inclusion is exactly the original ordinal-sum map. -/
theorem prefixBoundaryMap_comp_inclusion (k : ℕ) {m n : SimplexCategory} (α : m ⟶ n) :
    prefixBoundaryMap.{u} k α ≫ (prefixBoundary k n.len).ι =
      (prefixBoundary k m.len).ι ≫ SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map α) :=
  SSet.Subcomplex.lift_ι _ _

/-- At every degree, the underlying simplex is the image under that exact original operator. -/
theorem prefixBoundaryMap_app_val (k : ℕ) {m n : SimplexCategory} (α : m ⟶ n)
    (q : SimplexCategoryᵒᵖ) (s : (prefixBoundary k m.len : SSet.{u}).obj q) :
    ((prefixBoundaryMap k α).app q s).val =
      (SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map α)).app q s.val := rfl

/-- The joined prefix boundaries and their original maps form an actual cosimplicial object. -/
def prefixBoundaryFunctor (k : ℕ) : SimplexCategory ⥤ SSet.{u} where
  obj n := (prefixBoundary k n.len : SSet.{u})
  map α := prefixBoundaryMap k α
  map_id n := by
    apply (cancel_mono (prefixBoundary k n.len).ι).mp
    rw [prefixBoundaryMap_comp_inclusion]
    rw [(ordinalJoinLeft ⦋k⦌).map_id n,
      CategoryTheory.Functor.map_id SSet.stdSimplex ((ordinalJoinLeft ⦋k⦌).obj n)]
    exact (Category.comp_id (prefixBoundary k n.len).ι).trans
      (Category.id_comp (prefixBoundary k n.len).ι).symm
  map_comp {a b c} α β := by
    apply (cancel_mono (prefixBoundary k c.len).ι).mp
    rw [prefixBoundaryMap_comp_inclusion, Category.assoc,
      prefixBoundaryMap_comp_inclusion, ← Category.assoc,
      prefixBoundaryMap_comp_inclusion]
    simp only [Functor.map_comp, Category.assoc]

end

end DaggerOriginalJoinedPrefixBoundaryFunctor
