import OriginalAllPrefixBoundaryInvertibleLifting

/-!
# Exact original prefix-boundary and suffix-face inclusions in the right outer horn

In the original joined simplex [k] join [1], every omitted-prefix face and
the original suffix-zero face belong to the original right outer horn. Their
lifted inclusions retain the actual original ambient operators. The last-edge
inclusion is the original native right-block map, with no endpoint replacement.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedCofaces
open DaggerOriginalJoinedPrefixBoundaryFunctor DaggerOriginalJoinedBoundarySuffixInclusion
open DaggerOriginalRestBoundaryInverseFaceMaps

universe u

namespace DaggerOriginalRightOuterHornInclusions

noncomputable section

/-- Every original omitted-prefix face is included in the actual right outer horn. -/
theorem prefixBoundary_le_rightOuterHorn (k : ℕ) :
    prefixBoundary.{u} k 1 ≤ Λ[k + 2, Fin.last (k + 2)] := by
  rw [prefixBoundary, iSup_le_iff]
  intro j
  apply SSet.face_le_horn
  intro h
  have hv := congrArg Fin.val h
  change j.val = k + 2 at hv
  have hj := j.isLt
  omega

/-- The original boundary inclusion into the actual right outer horn. -/
def rightOuterBoundaryInclusion (k : ℕ) :
    (prefixBoundary k 1 : SSet.{u}) ⟶ (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (prefixBoundary_le_rightOuterHorn k)

/-- Following the inclusion is exactly the original smaller boundary ambient inclusion. -/
theorem rightOuterBoundaryInclusion_comp (k : ℕ) :
    rightOuterBoundaryInclusion.{u} k ≫ Λ[k + 2, Fin.last (k + 2)].ι =
      (prefixBoundary k 1).ι :=
  SSet.Subcomplex.homOfLE_ι (prefixBoundary_le_rightOuterHorn k)

/-- The original suffix-zero face differs from the actual omitted last face. -/
theorem rightOuterSuffixZero_ne_last (k : ℕ) :
    suffixIndex k 1 0 ≠ Fin.last (k + 2) := by
  intro h
  have hv := congrArg Fin.val h
  change k + 1 + 0 = k + 2 at hv
  omega

/-- The exact original suffix-zero joined face in the actual right outer horn. -/
def rightOuterJoinedFaceInclusion (k : ℕ) :
    SSet.stdSimplex.obj ((ordinalJoinLeft ⦋k⦌).obj ⦋0⦌) ⟶
      (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) :=
  SSet.horn.ι (Fin.last (k + 2)) (suffixIndex k 1 0) (rightOuterSuffixZero_ne_last k)

/-- Its ambient operator is the actual native suffix-zero joined coface. -/
theorem rightOuterJoinedFaceInclusion_comp (k : ℕ) :
    rightOuterJoinedFaceInclusion.{u} k ≫ Λ[k + 2, Fin.last (k + 2)].ι =
      SSet.stdSimplex.map ((ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ (n := 0) 0)) := by
  rw [rightOuterJoinedFaceInclusion, SSet.horn.ι_ι]
  have h := joinMap_coface k 0 0
  change (ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ (n := 0) 0) =
    SimplexCategory.δ (suffixIndex k 1 0) at h
  rw [h]
  rfl

/-- The whole original boundary restriction commutes with the original suffix-zero face. -/
theorem rightOuterBoundary_face_square (k : ℕ) :
    prefixBoundaryMap.{u} k (SimplexCategory.δ (n := 0) 0) ≫ rightOuterBoundaryInclusion k =
      (prefixBoundary k 0).ι ≫ rightOuterJoinedFaceInclusion k := by
  apply (cancel_mono Λ[k + 2, Fin.last (k + 2)].ι).mp
  have hmap := prefixBoundaryMap_comp_inclusion.{u} k (SimplexCategory.δ (n := 0) 0)
  simp only [SimplexCategory.len_mk] at hmap
  rw [Category.assoc, rightOuterBoundaryInclusion_comp, hmap,
    Category.assoc, rightOuterJoinedFaceInclusion_comp]

/-- The actual last edge inside the original right outer horn, using its native right block. -/
def rightOuterLastEdgeInclusion (k : ℕ) :
    (Δ[1] : SSet.{u}) ⟶ (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) :=
  boundarySuffixInclusion k ⦋1⦌ ≫ rightOuterBoundaryInclusion k

/-- Its original ambient operator is exactly the actual native original last-edge inclusion. -/
theorem rightOuterLastEdgeInclusion_comp (k : ℕ) :
    rightOuterLastEdgeInclusion.{u} k ≫ Λ[k + 2, Fin.last (k + 2)].ι =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋1⦌) := by
  rw [rightOuterLastEdgeInclusion, Category.assoc, rightOuterBoundaryInclusion_comp]
  simpa only [SimplexCategory.len_mk] using boundarySuffixInclusion_comp.{u} k ⦋1⦌

end

end DaggerOriginalRightOuterHornInclusions
