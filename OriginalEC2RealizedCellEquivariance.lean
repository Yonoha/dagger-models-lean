import OriginalEC2RealizedCellOrbits
import OriginalEC2RealizationAction

/-!
# Equivariance of the actual realized `EC₂` characteristic maps

The original left regular action sends the cell indexed by `g` to the cell
indexed by `h * g`. Both maps have the same genuine realized simplex domain.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2NondegenerateFreeOrbit
open DaggerOriginalEC2NondegenerateOrbit
open DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2RealizedCellOrbits

universe u

namespace DaggerOriginalEC2RealizedCellEquivariance

noncomputable section

/-- Applying `h` to the original `g`-cell yields the `(h * g)`-cell in
the same simplicial degree. -/
theorem orbitMap_action (n : ℕ) (h g : C2.{u}) :
    (((simplicialAction.{u}.ρ h).asHom).app (op ⦋n⦌)
      (orbitMap.{u} n g).val) =
        (orbitMap.{u} n (h * g)).val := by
  apply nondegenerate_eq_of_first n
    _ _ (action_nondegenerate h n (orbitMap n g).val (orbitMap n g).property)
    (orbitMap n (h * g)).property
  let v : C2.{u} :=
    ((DaggerOriginalEC2NondegenerateRepresentative.representative.{u} n).obj 0).as
  change Codiscrete.mk (h * (g * v)) = Codiscrete.mk ((h * g) * v)
  exact congrArg (Codiscrete.mk : C2.{u} → Codiscrete C2.{u}) (mul_assoc h g v).symm

/-- The characteristic map of a literal cell commutes with the actual
realized action and left multiplication on its `C₂` index. -/
theorem realizedCell_characteristic_equivariant (n : ℕ) (h g : C2.{u}) :
    ((realizedCellsEquiv.{u}).symm ⟨n, g⟩).ι ≫
      (realizedEC2Action.{u}.ρ h).asHom =
        ((realizedCellsEquiv.{u}).symm ⟨n, h * g⟩).ι := by
  rw [realizedCell_characteristic, realizedCell_characteristic,
    realizedEC2Action_map, ← Functor.map_comp]
  rw [SSet.yonedaEquiv_symm_comp]
  rw [orbitMap_action]
  rfl

end

end DaggerOriginalEC2RealizedCellEquivariance
