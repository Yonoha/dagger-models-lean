import NativeRelativeHornMatchingComponents
import NativeBisimplicialColumnsFromMatching

/-! Actual Reedy and pi-Kan data imply fibrations in the original transverse direction. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialRelativeLifting
open DaggerNativeHorizontalPiSections DaggerNativeReedyFibrantHorizontalMapping
open DaggerNativeComponentMatchingNaturality DaggerNativeRelativeHornMatchingComponents
open DaggerNativeBisimplicialColumnsFromMatching
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePiKanReedyColumns
noncomputable section

theorem columns_fibration {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : ReedyFibration f)
    (hX : ReedyFibrant X) (hY : ReedyFibrant Y)
    (hπX : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection X (q + 1)))
    (hπY : ∀ q : ℕ, Fibration (C := SSet.{u}) (rowProjection Y (q + 1)))
    [Fibration (C := SSet.{u}) (componentMap f)] (v : SimplexCategoryᵒᵖ) :
    Fibration (C := SSet.{u}) ((flipMap f).app v) :=
  columns_fibration_of_horn_matching_components f hf
    (relative_horn_matching_components_surjective f hX hY hπX hπY) v

end
end DaggerNativePiKanReedyColumns
