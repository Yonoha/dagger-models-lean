import NativeBisimplicialDiagonal
import OriginalDiagonalGeometricRowReconciledRecovered
import NativeFamilyWeak

/-! Reuse the previously verified ORIGINAL diagonal weak theorem for every rowwise weak map. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialDiagonal
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBisimplicialDiagonalWeak
noncomputable section

theorem diagonal_map_weak {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ∀ h, WeakEquivalence (f.app h)) : WeakEquivalence (diagonalFunctor.map f) := by
  apply (weakEquivalence_iff_GW _).mpr
  exact DaggerOriginalDiagonalGeometric.diagMap_geometric_row f
    (fun h ↦ (weakEquivalence_iff_GW _).mp (hf h))

end
end DaggerNativeBisimplicialDiagonalWeak
