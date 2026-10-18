import ChallengeActualWeakAccessibility
import DaggerModels.FreeCofibrationClosure

/-! The literal rigidification preserves free cofibrations; WD has the required closures. -/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OrdinaryRigidification.DaggerRigidification
universe u

namespace DaggerActualLeftProperChallenge

abbrev D := DaggerSSet.{u}
abbrev weak : MorphismProperty D.{u} := DaggerActualWeakAccessibilityChallenge.weakD.{u}
abbrev cof : MorphismProperty D.{u} := DaggerSSet.freeCofibrations.{u}
abbrev trivialCof : MorphismProperty D.{u} := cof ⊓ weak

def rigidificationStatement : Prop :=
  ∀ {X Y : D.{u}} (i : X ⟶ Y), cof i →
    DaggerActualGlobalModelChallenge.generators.rlp.llp (daggerRigidification.map i)

def leftProperStatement : Prop :=
  ∀ {X Y X' Y' : D.{u}} {f : X ⟶ Y} {i : X ⟶ X'} {j : Y ⟶ Y'} {f' : X' ⟶ Y'},
    IsPushout f i j f' → cof i → weak f → weak f'

def closureStatement : Prop :=
  trivialCof.{u}.IsStableUnderCobaseChange ∧
    MorphismProperty.IsStableUnderTransfiniteComposition.{u} trivialCof.{u} ∧
    trivialCof.{u}.IsStableUnderRetracts

end DaggerActualLeftProperChallenge
