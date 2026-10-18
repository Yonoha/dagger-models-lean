import RectangularInverseWitnessData
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Whole cells with an actual fixed target descend uniquely through source colimits. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerNativeEndomorphismSimplexMaps DaggerRectangularInverseWitnessData
universe u vJ uJ
namespace DaggerColimitFixedTargetCells
noncomputable section
local instance nativeBraiding : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

local instance tensorRightPreserves (J : Type uJ) [Category.{vJ} J] (K : SSet.{u}) :
    PreservesColimitsOfShape J (tensorRight K) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

variable {J : Type uJ} [Category.{vJ} J] {F : J ⥤ SSet.{u}} {c : Cocone F}
  (Z : SSet.{u}) (n : ℕ) (s : ∀ j, ((ihom (F.obj j)).obj Z).obj (op ⦋n⦌))
  (hs : ∀ {i j} (f : i ⟶ j), simplexHomEquiv (F.obj i) Z n (s i) =
    F.map f ▷ Δ[n] ≫ simplexHomEquiv (F.obj j) Z n (s j))

def cellCocone : Cocone (F ⋙ tensorRight Δ[n]) where
  pt := Z
  ι :=
    { app := fun j ↦ simplexHomEquiv (F.obj j) Z n (s j)
      naturality := by
        intro i j f
        change F.map f ▷ Δ[n] ≫ simplexHomEquiv (F.obj j) Z n (s j) =
          simplexHomEquiv (F.obj i) Z n (s i) ≫ 𝟙 _
        rw [Category.comp_id]
        exact (hs f).symm }

def descMap (hc : IsColimit c) : c.pt ⊗ Δ[n] ⟶ Z :=
  (isColimitOfPreserves (tensorRight Δ[n]) hc).desc (cellCocone Z n s hs)

def descSimplex (hc : IsColimit c) : ((ihom c.pt).obj Z).obj (op ⦋n⦌) :=
  (simplexHomEquiv c.pt Z n).symm (descMap Z n s hs hc)

theorem descMap_fac (hc : IsColimit c) (j : J) :
    c.ι.app j ▷ Δ[n] ≫ descMap Z n s hs hc = simplexHomEquiv (F.obj j) Z n (s j) :=
  (isColimitOfPreserves (tensorRight Δ[n]) hc).fac (cellCocone Z n s hs) j

theorem descSimplex_square (hc : IsColimit c) (j : J) :
    Square (c.ι.app j) (𝟙 Z) (s j) (descSimplex Z n s hs hc) := by
  apply (square_iff_tensor_map _ _ _ _ _).2
  change simplexHomEquiv (F.obj j) Z n (s j) ≫ 𝟙 Z =
    c.ι.app j ▷ Δ[n] ≫
      simplexHomEquiv c.pt Z n ((simplexHomEquiv c.pt Z n).symm (descMap Z n s hs hc))
  rw [Equiv.apply_symm_apply, Category.comp_id]
  exact (descMap_fac Z n s hs hc j).symm

theorem descSimplex_unique (hc : IsColimit c) (y : ((ihom c.pt).obj Z).obj (op ⦋n⦌))
    (hy : ∀ j, Square (c.ι.app j) (𝟙 Z) (s j) y) : descSimplex Z n s hs hc = y := by
  apply (simplexHomEquiv c.pt Z n).injective
  rw [descSimplex, Equiv.apply_symm_apply]
  apply (isColimitOfPreserves (tensorRight Δ[n]) hc).hom_ext
  intro j
  have h := (square_iff_tensor_map _ _ _ _ _).1 (hy j)
  rw [Category.comp_id] at h
  exact (descMap_fac Z n s hs hc j).trans h

theorem descSimplex_target_square (hc : IsColimit c) {A B : SSet.{u}}
    (a : c.pt ⟶ A) (b : Z ⟶ B) (y : ((ihom A).obj B).obj (op ⦋n⦌))
    (hy : ∀ j, Square (c.ι.app j ≫ a) b (s j) y) :
    Square a b (descSimplex Z n s hs hc) y := by
  apply (square_iff_tensor_map _ _ _ _ _).2
  rw [descSimplex, Equiv.apply_symm_apply]
  apply (isColimitOfPreserves (tensorRight Δ[n]) hc).hom_ext
  intro j
  change (c.ι.app j ▷ Δ[n]) ≫ (descMap Z n s hs hc ≫ b) =
    (c.ι.app j ▷ Δ[n]) ≫ (a ▷ Δ[n] ≫ simplexHomEquiv A B n y)
  rw [← Category.assoc, descMap_fac]
  have h := (square_iff_tensor_map _ _ _ _ _).1 (hy j)
  exact h.trans (by rw [comp_whiskerRight, Category.assoc])

end
end DaggerColimitFixedTargetCells
