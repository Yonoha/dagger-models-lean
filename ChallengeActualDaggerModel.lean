import ChallengeActualWeakAccessibility
import DaggerModels.FreeCofibrationClosure

/-! Existence of the actual dagger model with the literal classes and small generators. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
universe u

namespace DaggerActualModelChallenge

abbrev D := DaggerSSet.{u}
abbrev weak : MorphismProperty D.{u} := DaggerActualWeakAccessibilityChallenge.weakD.{u}
abbrev cof : MorphismProperty D.{u} := DaggerSSet.freeCofibrations.{u}
abbrev boundaries : MorphismProperty D.{u} :=
  DaggerActualWeakAccessibilityChallenge.generators.{u}

def weakStructure : CategoryWithWeakEquivalences D.{u} := ⟨weak⟩
def cofibrationStructure : CategoryWithCofibrations D.{u} := ⟨cof⟩
def fibrationStructure : CategoryWithFibrations D.{u} := ⟨(cof ⊓ weak).rlp⟩

def statement : Prop :=
  ∃ M : ModelCategory D.{u},
    @ModelCategory.categoryWithWeakEquivalences D.{u} inferInstance M = weakStructure ∧
    @ModelCategory.categoryWithCofibrations D.{u} inferInstance M = cofibrationStructure ∧
    @ModelCategory.categoryWithFibrations D.{u} inferInstance M = fibrationStructure

def generationStatement : Prop :=
  IsLocallyPresentable.{u} D.{u} ∧ MorphismProperty.IsSmall.{u} boundaries.{u} ∧
    boundaries.{u}.rlp.llp = cof.{u} ∧
    ∃ J : MorphismProperty D.{u}, MorphismProperty.IsSmall.{u} J ∧ J.rlp.llp = cof ⊓ weak

end DaggerActualModelChallenge
