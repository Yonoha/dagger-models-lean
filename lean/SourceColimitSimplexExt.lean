import RectangularCellOperators
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Actual source-colimit legs jointly detect equality of whole internal-Hom simplices. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerNativeEndomorphismSimplexMaps DaggerRectangularInverseWitnessData
universe u uJ vJ
namespace DaggerSourceColimitSimplexExt
local instance nativeBraiding : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory
local instance tensorRightPreserves (J : Type uJ) [Category.{vJ} J] (K : SSet.{u}) :
    PreservesColimitsOfShape J (tensorRight K) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

theorem pre_ext {J : Type uJ} [Category.{vJ} J] {F : J ⥤ SSet.{u}} {c : Cocone F}
    (hc : IsColimit c) {Z : SSet.{u}} (n : ℕ)
    (s t : ((ihom c.pt).obj Z).obj (op ⦋n⦌))
    (h : ∀ j, ((MonoidalClosed.pre (c.ι.app j)).app Z).app (op ⦋n⦌) s =
      ((MonoidalClosed.pre (c.ι.app j)).app Z).app (op ⦋n⦌) t) : s = t := by
  apply (simplexHomEquiv c.pt Z n).injective
  apply (isColimitOfPreserves (tensorRight Δ[n]) hc).hom_ext
  intro j
  have hh := congrArg (simplexHomEquiv (F.obj j) Z n) (h j)
  simpa only [simplexHomEquiv_pre] using hh

theorem square_ext {J : Type uJ} [Category.{vJ} J] {F : J ⥤ SSet.{u}} {c : Cocone F}
    (hc : IsColimit c) {Z : SSet.{u}} (n : ℕ) (B : J → SSet.{u})
    (b : ∀ j, B j ⟶ Z) (x : ∀ j, ((ihom (F.obj j)).obj (B j)).obj (op ⦋n⦌))
    (s t : ((ihom c.pt).obj Z).obj (op ⦋n⦌))
    (hs : ∀ j, Square (c.ι.app j) (b j) (x j) s)
    (ht : ∀ j, Square (c.ι.app j) (b j) (x j) t) : s = t :=
  pre_ext hc n s t (fun j ↦ (hs j).symm.trans (ht j))

end DaggerSourceColimitSimplexExt
