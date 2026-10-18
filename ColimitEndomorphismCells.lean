import NativeEndomorphismSimplexMaps
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Actual native endomorphism simplices descend along colimit cocones

Decode simplices as maps with standard-simplex parameters. Tensor on the right
preserves the chosen colimit, so compatible whole cells have a unique colimit
cell, with exact strict squares along the original cocone maps.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerNativeEndomorphismCellSquares DaggerNativeEndomorphismSimplexMaps
universe u
namespace DaggerColimitEndomorphismCells
noncomputable section

local instance nativeBraiding : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

local instance tensorRightPreserves (J : Type u) [SmallCategory J] (K : SSet.{u}) :
    PreservesColimitsOfShape J (tensorRight K) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

variable {J : Type u} [SmallCategory J] {F : J ⥤ SSet.{u}} {c : Cocone F}
  (n : ℕ) (s : ∀ j, ((ihom (F.obj j)).obj (F.obj j)).obj (op ⦋n⦌))
  (hs : ∀ {i j} (f : i ⟶ j), CellSquare (F.map f) (s i) (s j))

def cellCocone : Cocone (F ⋙ tensorRight Δ[n]) where
  pt := c.pt
  ι :=
    { app := fun j ↦ simplexHomEquiv (F.obj j) (F.obj j) n (s j) ≫ c.ι.app j
      naturality := by
        intro i j f
        change (F.map f ▷ Δ[n]) ≫
          (simplexHomEquiv (F.obj j) (F.obj j) n (s j) ≫ c.ι.app j) =
            simplexHomEquiv (F.obj i) (F.obj i) n (s i) ≫ c.ι.app i
        have h := (cellSquare_iff_tensor_map_square (F.map f) n (s i) (s j)).1 (hs f)
        rw [← Category.assoc, ← h, Category.assoc, c.w f] }

def descMap (hc : IsColimit c) : c.pt ⊗ Δ[n] ⟶ c.pt :=
  (isColimitOfPreserves (tensorRight Δ[n]) hc).desc (cellCocone n s hs)

def descSimplex (hc : IsColimit c) : ((ihom c.pt).obj c.pt).obj (op ⦋n⦌) :=
  (simplexHomEquiv c.pt c.pt n).symm (descMap n s hs hc)

theorem descMap_fac (hc : IsColimit c) (j : J) :
    (c.ι.app j ▷ Δ[n]) ≫ descMap n s hs hc =
      simplexHomEquiv (F.obj j) (F.obj j) n (s j) ≫ c.ι.app j :=
  (isColimitOfPreserves (tensorRight Δ[n]) hc).fac (cellCocone n s hs) j

theorem descSimplex_square (hc : IsColimit c) (j : J) :
    CellSquare (c.ι.app j) (s j) (descSimplex n s hs hc) := by
  apply (cellSquare_iff_tensor_map_square _ n _ _).2
  change simplexHomEquiv (F.obj j) (F.obj j) n (s j) ≫ c.ι.app j =
    (c.ι.app j ▷ Δ[n]) ≫
      simplexHomEquiv c.pt c.pt n ((simplexHomEquiv c.pt c.pt n).symm (descMap n s hs hc))
  rw [Equiv.apply_symm_apply]
  exact (descMap_fac n s hs hc j).symm

theorem descSimplex_unique (hc : IsColimit c)
    (y : ((ihom c.pt).obj c.pt).obj (op ⦋n⦌))
    (hy : ∀ j, CellSquare (c.ι.app j) (s j) y) : descSimplex n s hs hc = y := by
  apply (simplexHomEquiv c.pt c.pt n).injective
  change simplexHomEquiv c.pt c.pt n
    ((simplexHomEquiv c.pt c.pt n).symm (descMap n s hs hc)) = simplexHomEquiv c.pt c.pt n y
  rw [Equiv.apply_symm_apply]
  apply (isColimitOfPreserves (tensorRight Δ[n]) hc).hom_ext
  intro j
  exact (descMap_fac n s hs hc j).trans
    ((cellSquare_iff_tensor_map_square _ n _ _).1 (hy j))

theorem descSimplex_target_square (hc : IsColimit c) {Z : SSet.{u}} (a : c.pt ⟶ Z)
    (y : ((ihom Z).obj Z).obj (op ⦋n⦌))
    (hy : ∀ j, CellSquare (c.ι.app j ≫ a) (s j) y) :
    CellSquare a (descSimplex n s hs hc) y := by
  apply (cellSquare_iff_tensor_map_square _ n _ _).2
  change simplexHomEquiv c.pt c.pt n
      ((simplexHomEquiv c.pt c.pt n).symm (descMap n s hs hc)) ≫ a =
    a ▷ Δ[n] ≫ simplexHomEquiv Z Z n y
  rw [Equiv.apply_symm_apply]
  apply (isColimitOfPreserves (tensorRight Δ[n]) hc).hom_ext
  intro j
  change (c.ι.app j ▷ Δ[n]) ≫ (descMap n s hs hc ≫ a) =
    (c.ι.app j ▷ Δ[n]) ≫ (a ▷ Δ[n] ≫ simplexHomEquiv Z Z n y)
  rw [← Category.assoc, descMap_fac, Category.assoc]
  have h := (cellSquare_iff_tensor_map_square _ n _ _).1 (hy j)
  exact h.trans (by rw [comp_whiskerRight, Category.assoc])

end
end DaggerColimitEndomorphismCells
