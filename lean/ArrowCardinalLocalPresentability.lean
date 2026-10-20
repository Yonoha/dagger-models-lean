import OriginalRLPArrowRecovered
import Mathlib.CategoryTheory.Presentable.Presheaf

/-! The original arrow category is locally presentable at the same regular rank. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerArrowCardinalLocalPresentability
noncomputable section

theorem atRank (C : Type w) [Category.{v} C] [HasPullbacks C]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable.{u} C κ] :
    IsCardinalLocallyPresentable.{u} (Arrow C) κ := by
  let K := ULiftHom (ULift.{u} (Fin 2))
  let e : (Kᵒᵖᵒᵖ ⥤ C) ≌ (K ⥤ C) := (opOpEquivalence K).congrLeft
  have : IsCardinalLocallyPresentable.{u} (Kᵒᵖᵒᵖ ⥤ C) κ := inferInstance
  have : IsCardinalLocallyPresentable.{u} (K ⥤ C) κ := e.isCardinalLocallyPresentable κ
  exact (DaggerRLPAccessibility.arrowSmallEquivalence.{u} C).symm.isCardinalLocallyPresentable κ

end
end DaggerArrowCardinalLocalPresentability
