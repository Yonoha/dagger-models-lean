import OriginalCounitRightConeQPushoutSimplexSupportReconciled
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Base/tip collision in the literal collapsed-face right cone

The large-simplex leg is not injective on the attaching face. This module
identifies exactly when one of its points equals a collapsed-base point:
precisely when the large-simplex operator belongs to the attaching face.
The proof uses the actual pointwise pushout and injectivity of the standard
last-face inclusion, not a replacement model for the right cone.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeQPushoutSimplexSupport

universe u

namespace DaggerOriginalCounitRightConeQBaseTipCollision

noncomputable section

/-- Postcomposition by a simplex-category monomorphism is injective on
every simplex degree of the corresponding standard simplicial sets. -/
theorem stdSimplex_map_app_injective {m n : SimplexCategory}
    (α : m ⟶ n) [Mono α] (q : SimplexCategoryᵒᵖ) :
    Function.Injective ((SSet.stdSimplex.map α :
      (SSet.stdSimplex.obj m : SSet.{u}) ⟶ SSet.stdSimplex.obj n).app q) := by
  intro x y h
  apply SSet.stdSimplex.objEquiv.injective
  have h' := congrArg SSet.stdSimplex.objEquiv h
  change SSet.stdSimplex.objEquiv x ≫ α =
    SSet.stdSimplex.objEquiv y ≫ α at h'
  exact (cancel_mono α).1 h'

/-- Exactly the attaching-face simplices of the large simplex collide with
the collapsed base in the original cone pushout. -/
theorem simplexIncl_mem_base_iff (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (y : (Δ[n + 1] : SSet.{u}).obj q) :
    (simplexIncl.{u} n).app q y ∈
        Set.range ((baseIncl.{u} n).app q) ↔
      y ∈ Set.range ((face.{u} n).app q) := by
  have hface : Function.Injective ((face.{u} n).app q) := by
    change Function.Injective
      ((SSet.stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1))) :
        (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]).app q)
    exact stdSimplex_map_app_injective.{u}
      (SimplexCategory.δ (Fin.last (n + 1))) q
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨s, hs, _⟩ :=
      (CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
        (cone_pointwise_isPushout.{u} n q).isColimit hface y b).1 hb.symm
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    refine ⟨(collapse.{u} n).app q s, ?_⟩
    exact (congrFun (NatTrans.congr_app (face_eq_collapse.{u} n) q) s).symm

end

end DaggerOriginalCounitRightConeQBaseTipCollision
