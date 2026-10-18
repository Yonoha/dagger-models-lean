import DaggerModels.DaggerGeneratingCofibrations
import OriginalUnitaryFibrantReplacementRecovered
import OriginalActualAcyclicGeneratorDefinitionsRecovered
import TopCatModelCategory.TopPackage

/-! A model structure with the original classes and finite generating domains. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
universe u

namespace DaggerActualGlobalModelChallenge

abbrev G := DaggerSimplicialCat.{u, u}
abbrev generators : MorphismProperty G.{u} := DaggerGeneratingCofibrations.generators.{u}
abbrev acyclic : MorphismProperty G.{u} := DaggerGlobalJLifting.J.{u}

abbrev weak : MorphismProperty G.{u} :=
  fun {C D} f ↦
    (∀ (x y : C.Obj),
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.map x y)))) ∧
    ∀ (d : D.Obj), ∃ c v,
      DaggerUnitaryInvariance.CoherentlyUnitary
        DaggerUnitaryInvariance.standardReplacement D (f.obj c) d v

def cofibrationStructure : CategoryWithCofibrations G.{u} := ⟨generators.rlp.llp⟩
def fibrationStructure : CategoryWithFibrations G.{u} := ⟨acyclic.rlp⟩
def weakStructure : CategoryWithWeakEquivalences G.{u} := ⟨weak⟩

def statement : Prop :=
  ∃ M : ModelCategory G.{u},
    @ModelCategory.categoryWithCofibrations G.{u} inferInstance M = cofibrationStructure ∧
    @ModelCategory.categoryWithFibrations G.{u} inferInstance M = fibrationStructure ∧
    @ModelCategory.categoryWithWeakEquivalences G.{u} inferInstance M = weakStructure

def finiteGenerationStatement : Prop :=
  IsLocallyFinitelyPresentable.{u, u, u + 1} G.{u} ∧
    MorphismProperty.IsSmall.{u, u, u + 1} generators.{u} ∧
    MorphismProperty.IsSmall.{u, u, u + 1} acyclic.{u} ∧
    (∀ {C D : G.{u}} (f : C ⟶ D), generators f → IsFinitelyPresentable.{u} C) ∧
    (∀ {C D : G.{u}} (f : C ⟶ D), acyclic f → IsFinitelyPresentable.{u} C)

end DaggerActualGlobalModelChallenge
