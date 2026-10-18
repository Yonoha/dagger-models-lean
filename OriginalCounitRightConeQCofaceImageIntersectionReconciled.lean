import OriginalCounitRightConeQNonbaseCofaceIntersectionReconciled
import OriginalCounitRightConeQJoinedFaceIntersectionReconciled

/-!
# Pointwise intersection of two literal right-cone coface images

The collapsed base belongs to every cone coface image. Away from it,
the intersection is the large-simplex codimension-two face, mapped
through the actual pushout leg `simplexIncl`. This theorem deliberately
keeps the base as a separate summand: `simplexIncl` is not globally
injective on the attaching face.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQPointwiseMapImage
open DaggerOriginalCounitRightConeQNonbaseCofaceIntersection
open DaggerOriginalCounitRightConeQJoinedFaceIntersection

universe u

namespace DaggerOriginalCounitRightConeQCofaceImageIntersection

noncomputable section

/-- The two original cone cofaces intersect in their common collapsed
base and in the image of the codimension-two large-simplex face. -/
theorem coface_pointwise_common_image_iff (k : ℕ) (i j : Fin (k + 2))
    (q : SimplexCategoryᵒᵖ) (x : (cone.{u} (k + 1)).obj q) :
    (x ∈ Set.range ((coneMap.{u} (SimplexCategory.δ i)).app q) ∧
      x ∈ Set.range ((coneMap.{u} (SimplexCategory.δ j)).app q)) ↔
      x ∈ Set.range ((baseIncl.{u} (k + 1)).app q) ∨
        ∃ y : (Δ[k + 2] : SSet.{u}).obj q,
          y ∈ (SSet.stdSimplex.face.{u}
            ({i.castSucc}ᶜ ⊓ {j.castSucc}ᶜ)).obj q ∧
            (simplexIncl.{u} (k + 1)).app q y = x := by
  have hface (y : (Δ[k + 2] : SSet.{u}).obj q) :
      (y ∈ Set.range ((joinMap.{u} (SimplexCategory.δ i)).app q) ∧
        y ∈ Set.range ((joinMap.{u} (SimplexCategory.δ j)).app q)) ↔
          y ∈ (SSet.stdSimplex.face.{u}
            ({i.castSucc}ᶜ ⊓ {j.castSucc}ᶜ)).obj q := by
    have h := congrArg
      (fun A : SSet.Subcomplex (Δ[k + 2] : SSet.{u}) ↦ y ∈ A.obj q)
      (joinMap_coface_range_inter.{u} k i j)
    simpa only [Subfunctor.min_obj, Subfunctor.range_obj,
      Set.mem_inter_iff] using (iff_of_eq h)
  by_cases hb : x ∈ Set.range ((baseIncl.{u} (k + 1)).app q)
  · constructor
    · intro _
      exact Or.inl hb
    · intro _
      constructor
      · exact (coneMap_pointwise_range_iff.{u}
          (SimplexCategory.δ i) q x).2 (Or.inl hb)
      · exact (coneMap_pointwise_range_iff.{u}
          (SimplexCategory.δ j) q x).2 (Or.inl hb)
  · rw [coface_nonbase_common_image_iff.{u} k i j q x hb]
    constructor
    · rintro ⟨y, hi, hj, hyx⟩
      exact Or.inr ⟨y, (hface y).1 ⟨hi, hj⟩, hyx⟩
    · rintro (h | ⟨y, hy, hyx⟩)
      · exact False.elim (hb h)
      · rcases (hface y).2 hy with ⟨hi, hj⟩
        exact ⟨y, hi, hj, hyx⟩

end

end DaggerOriginalCounitRightConeQCofaceImageIntersection
