import OriginalRealizationLocallyCompactProducts
import OriginalTopCatProductDeformationRetract

/-!
# Underlying cofibrations of the literal original EC₂ generator products

The original EC₂ is the realization of its original simplicial nerve. The
locally compact realized boundary and horn parameters therefore allow the
native product comparison to identify the original maps with realized
simplicial monomorphisms. The horn also retains its proved deformation
retract. These are assertions on underlying spaces; Borel action cofibrations
still require their equivariant lifting argument.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEquivariantParameterTensor DaggerOriginalEC2SimplicialAction
open DaggerOriginalRealizationLocallyCompactProducts DaggerOriginalEC2GeneratorLifting
open DaggerOriginalTopCatProductDeformationRetract DaggerOriginalBorelModelCategory

universe u

namespace DaggerOriginalEC2ProductUnderlyingCofibrations

noncomputable section

/-- The literal original EC₂ boundary product is a cofibration on underlying spaces. -/
theorem actualEC2BoundaryProduct_underlyingCofibration (n : ℕ) :
    Cofibration (parameterTensorMap realizedEC2ContinuousAction.{u}
      (SSet.toTop.map (SSet.boundary n).ι)).hom := by
  change Cofibration (SSet.toTop.obj simplicialEC2 ◁ SSet.toTop.map (SSet.boundary n).ι)
  exact realization_rightProduct_cofibration simplicialEC2 _

/-- The literal original EC₂ horn product is a cofibration on underlying spaces. -/
theorem actualEC2HornProduct_underlyingCofibration (n : ℕ) (i : Fin (n + 2)) :
    Cofibration (parameterTensorMap realizedEC2ContinuousAction.{u}
      (SSet.toTop.map (SSet.horn (n + 1) i).ι)).hom := by
  change Cofibration
    (SSet.toTop.obj simplicialEC2 ◁ SSet.toTop.map (SSet.horn (n + 1) i).ι)
  exact realization_rightProduct_cofibration simplicialEC2 _

/-- The literal original EC₂ horn product is an underlying trivial cofibration. -/
theorem actualEC2HornProduct_underlyingTrivialCofibration (n : ℕ) (i : Fin (n + 2)) :
    trivialCofibrations TopCat.{u} (parameterTensorMap realizedEC2ContinuousAction.{u}
      (SSet.toTop.map (SSet.horn (n + 1) i).ι)).hom := by
  apply (mem_trivialCofibrations_iff _).2
  exact ⟨actualEC2HornProduct_underlyingCofibration n i,
    (weakEquivalence_iff_underlying _).1 (actualEC2HornProduct_weakEquivalence n i)⟩

end

end DaggerOriginalEC2ProductUnderlyingCofibrations
