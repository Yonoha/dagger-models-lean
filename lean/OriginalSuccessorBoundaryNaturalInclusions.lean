import OriginalPrefixBoundaryConeTransposition

/-!
# Original inclusions in the successor-boundary square are natural

The retained first-face, remaining-face and whole-overlap maps commute with
all original suffix operators. Their ambient equations use the original
native join maps and the exact first-prefix coface, in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalPrefixDeleteFirstCoface DaggerOriginalPrefixDeleteFirstNativeJoin
open DaggerOriginalPrefixBoundarySuccessorIsomorphisms
open DaggerOriginalPrefixBoundarySuccessorMappingPullback
open DaggerOriginalRestPrefixBoundaryFunctor

universe u

namespace DaggerOriginalSuccessorBoundaryNaturalInclusions

noncomputable section

/-- The retained first-face inclusion has exactly the original coface as its ambient map. -/
theorem firstFaceBoundaryInclusion_comp_inclusion (k n : ℕ) :
    firstFaceBoundaryInclusion.{u} k n ≫ (prefixBoundary (k + 1) n).ι =
      prefixDeleteFirstMap k n := by
  rw [firstFaceBoundaryInclusion, Category.assoc, SSet.Subcomplex.homOfLE_ι,
    firstPrefixFaceIso_hom_comp]

/-- The first-face inclusion commutes with every original suffix operator. -/
theorem firstFaceBoundaryInclusion_naturality (k : ℕ) {m n : SimplexCategory}
    (β : m ⟶ n) :
    SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map β) ≫
        firstFaceBoundaryInclusion.{u} k n.len =
      firstFaceBoundaryInclusion k m.len ≫ prefixBoundaryMap (k + 1) β := by
  induction m using SimplexCategory.rec with | h m =>
    induction n using SimplexCategory.rec with | h n =>
      have hmap := prefixBoundaryMap_comp_inclusion.{u} (k + 1) β
      simp only [SimplexCategory.len_mk] at hmap
      apply (cancel_mono (prefixBoundary (k + 1) n).ι).mp
      simp only [SimplexCategory.len_mk]
      rw [Category.assoc, firstFaceBoundaryInclusion_comp_inclusion,
        Category.assoc, hmap, ← Category.assoc,
        firstFaceBoundaryInclusion_comp_inclusion]
      dsimp only [prefixDeleteFirstMap]
      rw [← Functor.map_comp, ← Functor.map_comp, prefixDeleteFirstOperator_naturality]

/-- The original whole-overlap embedding commutes with every original suffix operator. -/
theorem boundaryToRest_naturality (k : ℕ) {m n : SimplexCategory} (β : m ⟶ n) :
    prefixBoundaryMap.{u} k β ≫ boundaryToRest k n.len =
      boundaryToRest k m.len ≫ restPrefixBoundaryMap k β := by
  induction m using SimplexCategory.rec with | h m =>
    induction n using SimplexCategory.rec with | h n =>
      have hmap := prefixBoundaryMap_comp_inclusion.{u} k β
      have hrest := restPrefixBoundaryMap_comp_inclusion.{u} k β
      simp only [SimplexCategory.len_mk] at hmap hrest
      apply (cancel_mono (restPrefixBoundary k n).ι).mp
      simp only [SimplexCategory.len_mk]
      rw [Category.assoc, boundaryToRest_comp_inclusion, ← Category.assoc, hmap]
      simp only [Category.assoc]
      rw [hrest, ← Category.assoc (boundaryToRest k m) (restPrefixBoundary k m).ι,
        boundaryToRest_comp_inclusion]
      dsimp only [prefixDeleteFirstMap]
      simp only [Category.assoc]
      rw [← Functor.map_comp, ← Functor.map_comp, prefixDeleteFirstOperator_naturality]


/-- The inclusion of the original remaining faces in the entire original successor boundary. -/
def restBoundaryInclusion (k n : ℕ) :
    (DaggerOriginalPrefixBoundarySuccessorShapes.restPrefixBoundary k n : SSet.{u}) ⟶
      prefixBoundary (k + 1) n :=
  SSet.Subcomplex.homOfLE (restPrefixBoundary_le_boundary k n)

/-- Its actual original ambient inclusion is retained. -/
theorem restBoundaryInclusion_comp_inclusion (k n : ℕ) :
    restBoundaryInclusion.{u} k n ≫ (prefixBoundary (k + 1) n).ι =
      (restPrefixBoundary k n).ι :=
  SSet.Subcomplex.homOfLE_ι (restPrefixBoundary_le_boundary k n)

/-- The remaining-face inclusion commutes with every original suffix operator. -/
theorem restBoundaryInclusion_naturality (k : ℕ) {m n : SimplexCategory} (β : m ⟶ n) :
    restPrefixBoundaryMap.{u} k β ≫ restBoundaryInclusion k n.len =
      restBoundaryInclusion k m.len ≫ prefixBoundaryMap (k + 1) β := by
  apply (cancel_mono (prefixBoundary (k + 1) n.len).ι).mp
  rw [Category.assoc, restBoundaryInclusion_comp_inclusion,
    restPrefixBoundaryMap_comp_inclusion, Category.assoc,
    prefixBoundaryMap_comp_inclusion, ← Category.assoc,
    restBoundaryInclusion_comp_inclusion]

end

end DaggerOriginalSuccessorBoundaryNaturalInclusions
