import OriginalActualDaggerCofibrationClass
import OriginalDaggerBoundaryWeakRecovered
import OriginalJoyalTrivialCofClosureRecovered
import OriginalJoyalLeftProperRecovered
import OriginalSmithModelRecovered
import OrdinaryRigidificationCof

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra DaggerModels
open DaggerUnitaryInvariance DaggerActualWeakAccessibility
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalJoyalModel

noncomputable section

attribute [local instance] DaggerJoyalWeakProperties.joyalTwoOutOfThree
attribute [local instance] DaggerJoyalWeakProperties.joyalRetractStable


private instance locallyPresentable : IsLocallyPresentable.{u} DaggerSSet.{u} :=
  NamespaceGate.actualDaggerSetLP

private instance smallOriginalID : MorphismProperty.IsSmall.{u} originalID.{u} :=
  originalID_small

private instance smithCobase (R : FunctorialFibrantReplacement.{u}) :
    (originalID.rlp.llp ⊓ WD R).IsStableUnderCobaseChange := by
  rw [originalID_rlp_llp_eq_freeCofibrations]
  exact DaggerJoyalTrivialCofClosure.cobaseStable R

private instance smithTransfinite (R : FunctorialFibrantReplacement.{u}) :
    IsStableUnderTransfiniteComposition.{u} (originalID.rlp.llp ⊓ WD R) := by
  rw [originalID_rlp_llp_eq_freeCofibrations]
  exact DaggerJoyalTrivialCofClosure.transfiniteStable R

/-- All Smith data use the literal free boundaries and original weak class. -/
def combinatorialData (R : FunctorialFibrantReplacement.{u}) :
    DaggerSmithSolutionSet.CombinatorialData
      (DaggerActualWeakAccessibility.solution R) :=
  DaggerSmithSolutionSet.combinatorialData
    (DaggerActualWeakAccessibility.solution R)
    (DaggerOriginalDaggerBoundaryWeak.freeBoundary_rlp_le_joyalWeakEquivalences R)

/-- The actual dagger Joyal model category, with no caller-supplied Smith data. -/
def modelCategory (R : FunctorialFibrantReplacement.{u}) : ModelCategory DaggerSSet.{u} :=
  (combinatorialData R).model

theorem model_weak (R : FunctorialFibrantReplacement.{u}) :
    (modelCategory R).categoryWithWeakEquivalences.weakEquivalences = WD R :=
  (combinatorialData R).modelWeak

theorem model_cof (R : FunctorialFibrantReplacement.{u}) :
    (modelCategory R).categoryWithCofibrations.cofibrations =
      DaggerSSet.freeCofibrations.{u} := by
  calc
    _ = originalID.rlp.llp := (combinatorialData R).modelCof
    _ = DaggerSSet.freeCofibrations := originalID_rlp_llp_eq_freeCofibrations

theorem model_fib (R : FunctorialFibrantReplacement.{u}) :
    (modelCategory R).categoryWithFibrations.fibrations =
      (DaggerSSet.freeCofibrations.{u} ⊓ WD R).rlp := by
  rw [(combinatorialData R).modelFib,
    originalID_rlp_llp_eq_freeCofibrations]

/-- Both trivial classes retain their exact original morphism predicates. -/
theorem model_trivialCofibrations (R : FunctorialFibrantReplacement.{u}) :
    (modelCategory R).categoryWithCofibrations.cofibrations ⊓
      (modelCategory R).categoryWithWeakEquivalences.weakEquivalences =
        DaggerSSet.freeCofibrations.{u} ⊓ WD R := by
  rw [model_cof R, model_weak R]

theorem model_trivialFibrations (R : FunctorialFibrantReplacement.{u}) :
    (modelCategory R).categoryWithFibrations.fibrations ⊓
      (modelCategory R).categoryWithWeakEquivalences.weakEquivalences =
        originalID.{u}.rlp := by
  rw [(combinatorialData R).modelFib, model_weak R]
  rw [← (combinatorialData R).fibrations]
  exact (combinatorialData R).trivialFibrations

theorem model_trivialFibrations_eq_cof_rlp
    (R : FunctorialFibrantReplacement.{u}) :
    (modelCategory R).categoryWithFibrations.fibrations ⊓
      (modelCategory R).categoryWithWeakEquivalences.weakEquivalences =
        DaggerSSet.freeCofibrations.{u}.rlp := by
  rw [model_trivialFibrations R, originalID_rlp_eq_freeCofibrations_rlp]

/-- The generated family is the actual small output of the Smith construction. -/
def generatedJ (R : FunctorialFibrantReplacement.{u}) :
    MorphismProperty DaggerSSet.{u} :=
  DaggerSmithSolutionSet.J (DaggerActualWeakAccessibility.solution R)

theorem generatedJ_small (R : FunctorialFibrantReplacement.{u}) :
    MorphismProperty.IsSmall.{u} (generatedJ R) :=
  (combinatorialData R).smallJ

def generatedJ_cardinal (R : FunctorialFibrantReplacement.{u}) :
    DaggerSmithSolutionSet.CardinalWitness.{u} (generatedJ R) :=
  (combinatorialData R).cardinalJ

theorem generatedJ_trivialCofibrations
    (R : FunctorialFibrantReplacement.{u}) :
    (generatedJ R).rlp.llp = DaggerSSet.freeCofibrations.{u} ⊓ WD R := by
  calc
    _ = originalID.rlp.llp ⊓ WD R := (combinatorialData R).trivialCofibrations
    _ = DaggerSSet.freeCofibrations ⊓ WD R := by
      rw [originalID_rlp_llp_eq_freeCofibrations]

/-- Literal boundary lifting is the original ordinary trivial-fibration test. -/
theorem boundary_lifting_iff_ordinary_trivial
    {X Y : DaggerSSet.{u}} (p : X ⟶ Y) :
    (∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι p.hom) ↔
      Fibration p.hom ∧ DaggerOrdinaryRigidificationCof.geometric p.hom :=
  (KanQuillenReuse.boundary_lifting_iff_rlp p.hom).trans
    (DaggerOrdinaryRigidificationCof.scalar_iff_rlp p.hom).symm

theorem trivialFibration_iff_boundary {X Y : DaggerSSet.{u}}
    (R : FunctorialFibrantReplacement.{u}) (p : X ⟶ Y) :
    (letI : ModelCategory DaggerSSet.{u} := modelCategory R
     trivialFibrations DaggerSSet.{u} p) ↔
      ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι p.hom := by
  change (((modelCategory R).categoryWithFibrations.fibrations ⊓
    (modelCategory R).categoryWithWeakEquivalences.weakEquivalences) p) ↔ _
  rw [model_trivialFibrations R]
  exact freeBoundary_rlp_iff freeDagger freeDaggerAdjunction p

theorem trivialFibration_iff_ordinary_trivial {X Y : DaggerSSet.{u}}
    (R : FunctorialFibrantReplacement.{u}) (p : X ⟶ Y) :
    (letI : ModelCategory DaggerSSet.{u} := modelCategory R
     trivialFibrations DaggerSSet.{u} p) ↔
      Fibration p.hom ∧ DaggerOrdinaryRigidificationCof.geometric p.hom :=
  (trivialFibration_iff_boundary R p).trans
    (boundary_lifting_iff_ordinary_trivial p)

/-- The full original T11 existence statement for every replacement. -/
theorem exists_modelCategory (R : FunctorialFibrantReplacement.{u}) :
    ∃ M : ModelCategory DaggerSSet.{u},
      M.categoryWithWeakEquivalences.weakEquivalences = WD R ∧
      M.categoryWithCofibrations.cofibrations = DaggerSSet.freeCofibrations ∧
      M.categoryWithFibrations.fibrations =
        (DaggerSSet.freeCofibrations ⊓ WD R).rlp :=
  ⟨modelCategory R, model_weak R, model_cof R, model_fib R⟩

def standardModelCategory : ModelCategory DaggerSSet.{u} :=
  modelCategory standardReplacement

def standardCombinatorialData :
    DaggerSmithSolutionSet.CombinatorialData
      (DaggerActualWeakAccessibility.standardSolution.{u}) :=
  combinatorialData standardReplacement

theorem standard_model_weak :
    standardModelCategory.{u}.categoryWithWeakEquivalences.weakEquivalences =
      DaggerJoyalWeakProperties.standardJoyalWeakEquivalences.{u} :=
  model_weak standardReplacement

theorem standard_model_cof :
    standardModelCategory.{u}.categoryWithCofibrations.cofibrations =
      DaggerSSet.freeCofibrations.{u} :=
  model_cof standardReplacement

theorem standard_model_fib :
    standardModelCategory.{u}.categoryWithFibrations.fibrations =
      (DaggerSSet.freeCofibrations.{u} ⊓
        DaggerJoyalWeakProperties.standardJoyalWeakEquivalences.{u}).rlp :=
  model_fib standardReplacement

/-- T12 concerns the same supplied square and the original weak equivalence. -/
theorem leftProper (R : FunctorialFibrantReplacement.{u})
    {X Y X' Y' : DaggerSSet.{u}} {f : X ⟶ Y} {i : X ⟶ X'}
    {j : Y ⟶ Y'} {f' : X' ⟶ Y'} (sq : IsPushout f i j f')
    (hf : WD R f) (hi : DaggerSSet.freeCofibrations i) : WD R f' :=
  DaggerJoyalLeftProper.leftProper R sq hi hf

end

end DaggerOriginalJoyalModel
