import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureCofibrant
import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-! Reuse Mathlib's cofibrant derivability structure in the opposite model category. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite Limits
universe u v

namespace DaggerNativeFibrantOppositeDerivability
noncomputable section
variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Native cofibrancy in the opposite model is exactly native fibrancy. -/
theorem isCofibrant_op_iff_isFibrant (X : C) : IsCofibrant (op X) ↔ IsFibrant X := by
  rw [isCofibrant_iff_of_isInitial (terminal.from X).op
    (initialOpOfTerminal terminalIsTerminal),
    cofibration_op_iff]

/-- The original model's fibrancy is recovered from each actual opposite cofibrant object. -/
theorem isFibrant_unop (X : Cᵒᵖ) [IsCofibrant X] : IsFibrant X.unop :=
  (isCofibrant_op_iff_isFibrant X.unop).mp inferInstance

variable (C) in
/-- Mathlib's literal opposite cofibrant inclusion, without a new weak-equivalence class. -/
def dualFibrantInclusion :
    LocalizerMorphism (weakEquivalences (CofibrantObject Cᵒᵖ)).op
      (weakEquivalences Cᵒᵖ).op :=
  (CofibrantObject.localizerMorphism Cᵒᵖ).op

variable (C) in
/-- The native theorem on cofibrant objects supplies the equivalence after localization. -/
theorem dualFibrantInclusion_isLocalizedEquivalence :
    (dualFibrantInclusion C).IsLocalizedEquivalence := by
  dsimp only [dualFibrantInclusion]
  infer_instance

variable (C) in
/-- The native left derivability theorem supplies its right counterpart by opposition. -/
theorem dualFibrantInclusion_isRightDerivabilityStructure :
    (dualFibrantInclusion C).IsRightDerivabilityStructure :=
  (LocalizerMorphism.isLeftDerivabilityStructure_iff_op
    (CofibrantObject.localizerMorphism Cᵒᵖ)).mp inferInstance

end
end DaggerNativeFibrantOppositeDerivability
