import OriginalEquivariantParameterTensor
import OriginalBorelModelCategory

/-!
# Products of the native original topological deformation retracts

The ordinary product with any original space retains the actual deformation
retract. Applied to the original realized horns, this proves weakness of the
literal EC₂ product arrow in the Borel model. Its cofibration assertion remains
separate and is not assumed here.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEquivariantParameterTensor DaggerOriginalBorelModelCategory

universe u

namespace DaggerOriginalTopCatProductDeformationRetract

noncomputable section

/-- An ordinary product retains the same native deformation in the original second factor. -/
def productDeformationRetract (E : TopCat.{u}) {A B : TopCat.{u}}
    (R : TopCat.DeformationRetract A B) : TopCat.DeformationRetract (E ⊗ A) (E ⊗ B) where
  i := E ◁ R.i
  r := E ◁ R.r
  retract := by
    rw [← whiskerLeft_comp, R.retract, whiskerLeft_id]
  h := (α_ E B TopCat.I).hom ≫ E ◁ R.h
  hi := by
    apply ConcreteCategory.hom_ext
    intro ⟨⟨e, a⟩, t⟩
    exact Prod.ext rfl (ConcreteCategory.congr_hom R.hi (a, t))
  h₀ := by
    apply ConcreteCategory.hom_ext
    intro ⟨e, b⟩
    exact Prod.ext rfl (ConcreteCategory.congr_hom R.h₀ b)
  h₁ := by
    apply ConcreteCategory.hom_ext
    intro ⟨e, b⟩
    exact Prod.ext rfl (ConcreteCategory.congr_hom R.h₁ b)

/-- Product deformation retains exactly the original product inclusion. -/
theorem productDeformationRetract_i (E : TopCat.{u}) {A B : TopCat.{u}}
    (R : TopCat.DeformationRetract A B) : (productDeformationRetract E R).i = E ◁ R.i := rfl

/-- The original realized horn product is a native deformation retract on underlying spaces. -/
theorem actualEC2HornProduct_deformationRetracts (n : ℕ) (i : Fin (n + 2)) :
    TopCat.deformationRetracts
      (parameterTensorMap realizedEC2ContinuousAction.{u}
        (SSet.toTop.map (SSet.horn (n + 1) i).ι)).hom := by
  refine ⟨productDeformationRetract realizedEC2ContinuousAction.obj.V
    (SSet.horn.deformationRetractToTopMap i), ?_⟩
  rw [productDeformationRetract_i, SSet.horn.deformationRetractToTopMap_i]
  rfl

/-- The original EC₂ horn product is a weak equivalence in the actual Borel model structure. -/
theorem actualEC2HornProduct_weakEquivalence (n : ℕ) (i : Fin (n + 2)) :
    WeakEquivalence (parameterTensorMap realizedEC2ContinuousAction.{u}
      (SSet.toTop.map (SSet.horn (n + 1) i).ι)) := by
  rw [weakEquivalence_iff_underlying, weakEquivalence_iff]
  exact TopCat.modelCategory.deformationRetracts_le_weakEquivalences _
    (actualEC2HornProduct_deformationRetracts n i)

end

end DaggerOriginalTopCatProductDeformationRetract
