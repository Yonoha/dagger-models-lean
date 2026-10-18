import NativePiKanReedyColumns
import NativeBisimplicialDiagonalFibration

/-! Original pi-Kan and component-map data now yield the genuine original diagonal fibration. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialDiagonal
open DaggerNativeHorizontalPiSections DaggerNativeReedyFibrantHorizontalMapping
open DaggerNativeComponentMatchingNaturality
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePiKanReedyDiagonal
noncomputable section

theorem diagonal_fibration {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : ReedyFibration f)
    (hX : ReedyFibrant X) (hY : ReedyFibrant Y)
    (hπX : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection X (q + 1)))
    (hπY : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection Y (q + 1)))
    [Fibration (C := SSet.{u}) (componentMap f)] :
    Fibration (C := SSet.{u}) (diagonalFunctor.map f) :=
  DaggerNativeBisimplicialDiagonalFibration.diagonal_fibration f hf
    (DaggerNativePiKanReedyColumns.columns_fibration f hf hX hY hπX hπY)

end
end DaggerNativePiKanReedyDiagonal
