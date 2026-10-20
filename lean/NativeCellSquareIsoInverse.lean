import NativeEndomorphismSimplexMaps
import InverseTriangleCellFamily

/-! Reversing a strict cell square along an actual isomorphism preserves every chosen cell. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerNativeEndomorphismCellSquares DaggerNativeEndomorphismSimplexMaps
open DaggerNativeHoIsoTriangles DaggerSimplexInverseWitnessCategory
open DaggerInverseTriangleCellFamily
universe u
namespace DaggerNativeCellSquareIsoInverse

theorem cellSquare_inverse {X Y : SSet.{u}} (e : X ≅ Y) (n : ℕ)
    (x : ((ihom X).obj X).obj (op ⦋n⦌)) (y : ((ihom Y).obj Y).obj (op ⦋n⦌))
    (h : CellSquare e.hom x y) : CellSquare e.inv y x := by
  apply (cellSquare_iff_tensor_map_square e.inv n y x).2
  have hh := (cellSquare_iff_tensor_map_square e.hom n x y).1 h
  let E := (tensorRight Δ[n]).mapIso e
  let sx := simplexHomEquiv X X n x
  let sy := simplexHomEquiv Y Y n y
  change sy ≫ e.inv = E.inv ≫ sx
  change sx ≫ e.hom = E.hom ≫ sy at hh
  calc
    sy ≫ e.inv = E.inv ≫ (E.hom ≫ sy) ≫ e.inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = E.inv ≫ (sx ≫ e.hom) ≫ e.inv := by rw [← hh]
    _ = E.inv ≫ sx := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem triangleSquare_inverse {X Y : SSet.{u}} (e : X ≅ Y)
    {x₀ x₁ : SSet.hoFunctor.obj ((ihom X).obj X)}
    {y₀ y₁ : SSet.hoFunctor.obj ((ihom Y).obj Y)}
    (d : IsoTriangles ((ihom X).obj X) x₀ x₁)
    (f : IsoTriangles ((ihom Y).obj Y) y₀ y₁)
    (h : TriangleSquare e.hom d f) : TriangleSquare e.inv f d := by
  apply (square_iff_all_cells _ _ _).2
  intro k
  exact cellSquare_inverse e k.degree (cell d k) (cell f k)
    ((square_iff_all_cells _ _ _).1 h k)

end DaggerNativeCellSquareIsoInverse
