import OriginalCounitRightConeQPointwiseMapImageReconciled
import OriginalCounitRightConeQOffFaceInjectionReconciled

/-!
# Non-base intersection of two literal cone-map images

Away from the collapsed base, a point in two cone-map images has one
unique large-simplex operator in the images of both corresponding
`joinMap`s. This isolates the remaining ordinary standard-simplex face
intersection calculation without replacing the original cone pushout.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQPointwiseMapImage
open DaggerOriginalCounitRightConeQBaseTipCollision
open DaggerOriginalCounitRightConeQOffFaceInjection

universe u

namespace DaggerOriginalCounitRightConeQNonbaseCofaceIntersection

noncomputable section

/-- The non-base part of the intersection of two actual cone-map images is
exactly one shared large-simplex operator in both joined-map images. -/
theorem coneMap_nonbase_common_image_iff
    {m₁ m₂ n : SimplexCategory} (α : m₁ ⟶ n) (β : m₂ ⟶ n)
    (q : SimplexCategoryᵒᵖ) (x : (cone.{u} n.len).obj q)
    (hbase : x ∉ Set.range ((baseIncl.{u} n.len).app q)) :
    (x ∈ Set.range ((coneMap.{u} α).app q) ∧
      x ∈ Set.range ((coneMap.{u} β).app q)) ↔
      ∃ y : (Δ[n.len + 1] : SSet.{u}).obj q,
        y ∈ Set.range ((joinMap.{u} α).app q) ∧
        y ∈ Set.range ((joinMap.{u} β).app q) ∧
          (simplexIncl.{u} n.len).app q y = x := by
  constructor
  · rintro ⟨hα, hβ⟩
    rcases (coneMap_pointwise_range_iff.{u} α q x).1 hα with
      hb | ⟨y, hy, hyx⟩
    · exact False.elim (hbase hb)
    rcases (coneMap_pointwise_range_iff.{u} β q x).1 hβ with
      hb | ⟨z, hz, hzx⟩
    · exact False.elim (hbase hb)
    have hyface : y ∉ Set.range ((face.{u} n.len).app q) := by
      intro h
      exact hbase (hyx ▸ (simplexIncl_mem_base_iff.{u} n.len q y).2 h)
    have hyz : y = z :=
      simplexIncl_injective_off_face.{u} n.len q y z hyface
        (hyx.trans hzx.symm)
    subst z
    exact ⟨y, hy, hz, hyx⟩
  · rintro ⟨y, hy, hz, hyx⟩
    constructor
    · exact (coneMap_pointwise_range_iff.{u} α q x).2 (Or.inr ⟨y, hy, hyx⟩)
    · exact (coneMap_pointwise_range_iff.{u} β q x).2 (Or.inr ⟨y, hz, hyx⟩)

/-- Specialization to two actual cosimplicial cofaces of the collapsed-face
right cone; the remaining `joinMap` intersection is in a standard simplex. -/
theorem coface_nonbase_common_image_iff
    (k : ℕ) (i j : Fin (k + 2))
    (q : SimplexCategoryᵒᵖ) (x : (cone.{u} (k + 1)).obj q)
    (hbase : x ∉ Set.range ((baseIncl.{u} (k + 1)).app q)) :
    (x ∈ Set.range ((coneMap.{u} (SimplexCategory.δ i)).app q) ∧
      x ∈ Set.range ((coneMap.{u} (SimplexCategory.δ j)).app q)) ↔
      ∃ y : (Δ[k + 2] : SSet.{u}).obj q,
        y ∈ Set.range ((joinMap.{u} (SimplexCategory.δ i)).app q) ∧
        y ∈ Set.range ((joinMap.{u} (SimplexCategory.δ j)).app q) ∧
          (simplexIncl.{u} (k + 1)).app q y = x := by
  exact coneMap_nonbase_common_image_iff.{u}
    (SimplexCategory.δ i) (SimplexCategory.δ j) q x hbase

end

end DaggerOriginalCounitRightConeQNonbaseCofaceIntersection
