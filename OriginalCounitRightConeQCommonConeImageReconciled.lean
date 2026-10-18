import OriginalCounitRightConeQCommonJoinedFaceRangeReconciled
import OriginalCounitRightConeQCofaceImageIntersectionReconciled

/-!
# Distinct coface intersection is the image of the actual smaller cone

For two distinct cofaces into `cone (n + 2)`, the pointwise intersection
of their images is exactly the image of the original pushout-cone map
from `cone n` induced by the common old face. The proof compares the
literal pushout pointwise-image formula with the already computed
large-simplex face. It makes no statement about flagged-necklace
quotient classes or boundary Q monicity.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQPointwiseMapImage
open DaggerOriginalCounitRightConeQCofaceImageIntersection
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQCommonJoinedFaceRange

universe u

namespace DaggerOriginalCounitRightConeQCommonConeImage

noncomputable section

/-- The literal smaller right cone has precisely the common pointwise
image of two distinct cofaces, including the collapsed base. -/
theorem commonConeMap_pointwise_range_iff (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) (q : SimplexCategoryᵒᵖ)
    (x : (cone.{u} (n + 2)).obj q) :
    x ∈ Set.range ((coneMap.{u} (commonBaseHom n i j hij)).app q) ↔
      (x ∈ Set.range ((coneMap.{u} (SimplexCategory.δ i)).app q) ∧
        x ∈ Set.range ((coneMap.{u} (SimplexCategory.δ j)).app q)) := by
  have hface (y : (Δ[n + 3] : SSet.{u}).obj q) :
      y ∈ Set.range ((joinMap.{u} (commonBaseHom n i j hij)).app q) ↔
        y ∈ (SSet.stdSimplex.face.{u}
          ({i.castSucc}ᶜ ⊓ {j.castSucc}ᶜ)).obj q := by
    have h := congrArg
      (fun A : SSet.Subcomplex (Δ[n + 3] : SSet.{u}) ↦ y ∈ A.obj q)
      (commonJoinMap_range_eq_face.{u} n i j hij)
    simpa only [Subfunctor.range_obj] using (iff_of_eq h)
  rw [coneMap_pointwise_range_iff.{u} (commonBaseHom n i j hij) q x,
    coface_pointwise_common_image_iff.{u} (n + 1) i j q x]
  constructor
  · rintro (hb | ⟨y, hy, hyx⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨y, (hface y).1 hy, hyx⟩
  · rintro (hb | ⟨y, hy, hyx⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨y, (hface y).2 hy, hyx⟩

end

end DaggerOriginalCounitRightConeQCommonConeImage
