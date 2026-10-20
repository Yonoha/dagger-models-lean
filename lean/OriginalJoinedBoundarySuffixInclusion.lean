import OriginalJoinedBoundaryRestriction

/-!
# The exact original right block inside every joined prefix boundary

The original right block omits every prefix vertex, so its native simplex
map factors through the actual prefix boundary. Native subcomplex lifting
retains the exact inclusion diagram. Every original simplex operator commutes
with this inclusion, by the native right-block ordinal-sum naturality law.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedPrefixBoundaryFunctor

universe u

namespace DaggerOriginalJoinedBoundarySuffixInclusion

noncomputable section

/-- Every simplex in the image of the original right block lies in the original boundary. -/
theorem suffix_range_le_prefixBoundary (k : ℕ) (n : SimplexCategory) :
    SSet.Subcomplex.range (SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋k⦌ n)) ≤
      prefixBoundary.{u} k n.len := by
  induction n using SimplexCategory.rec with | h n =>
    intro q s hs
    obtain ⟨t, rfl⟩ := hs
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h d =>
        apply (le_iSup (fun j : Fin (k + 1) ↦
          SSet.stdSimplex.face.{u} {prefixIndex k n j}ᶜ) 0)
        rw [SSet.stdSimplex.mem_face_iff]
        simp only [Finset.mem_compl, Finset.mem_singleton]
        intro a
        change (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋n⦌).toOrderHom
          (SSet.stdSimplex.asOrderHom t a) ≠ prefixIndex k n 0
        rw [← suffixIndex_eq_native]
        exact (prefixIndex_ne_suffixIndex k n 0 (SSet.stdSimplex.asOrderHom t a)).symm

/-- The original right-block inclusion lifted into the literal joined prefix boundary. -/
def boundarySuffixInclusion (k : ℕ) (n : SimplexCategory) :
    (SSet.stdSimplex.obj n : SSet.{u}) ⟶ (prefixBoundary k n.len : SSet.{u}) :=
  SSet.Subcomplex.lift (SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋k⦌ n))
    (suffix_range_le_prefixBoundary k n)

/-- Following the lifted inclusion is exactly the native original right-block simplex map. -/
theorem boundarySuffixInclusion_comp (k : ℕ) (n : SimplexCategory) :
    boundarySuffixInclusion.{u} k n ≫ (prefixBoundary k n.len).ι =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋k⦌ n) :=
  SSet.Subcomplex.lift_ι _ _

/-- The original lifted right block commutes with every native original simplex operator. -/
theorem boundarySuffixInclusion_naturality (k : ℕ) {m n : SimplexCategory} (α : m ⟶ n) :
    boundarySuffixInclusion.{u} k m ≫ prefixBoundaryMap k α =
      SSet.stdSimplex.map α ≫ boundarySuffixInclusion k n := by
  apply (cancel_mono (prefixBoundary k n.len).ι).mp
  rw [Category.assoc, prefixBoundaryMap_comp_inclusion,
    ← Category.assoc, boundarySuffixInclusion_comp,
    Category.assoc, boundarySuffixInclusion_comp]
  exact (SSet.stdSimplex.map_comp _ _).symm.trans
    ((congrArg SSet.stdSimplex.map (suffix_comp (k := ⦋k⦌) α)).trans
      (SSet.stdSimplex.map_comp _ _))

/-- The original right block is an actual natural transformation of the original shape functors. -/
def boundarySuffixNatural (k : ℕ) : SSet.stdSimplex.{u} ⟶ prefixBoundaryFunctor k where
  app n := boundarySuffixInclusion k n
  naturality _ _ α := (boundarySuffixInclusion_naturality k α).symm

end

end DaggerOriginalJoinedBoundarySuffixInclusion
