import ChallengeActualDaggerModelMain
import ActualDaggerRigidificationQuillen

/-! Independently require every clause of the manuscript's Theorem B for the same standard model. -/
set_option autoImplicit false
open HomotopicalAlgebra
universe u
namespace DaggerActualMainTheoremBChallenge
noncomputable section

local instance : ModelCategory DaggerActualRigidificationQuillen.D.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}
local instance : ModelCategory DaggerActualRigidificationQuillen.G.{u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

/-- Fix free cofibrations, the original weak class, small generators, left properness and trivial Kan fibrations. -/
def modelStatement : Prop :=
  DaggerActualModelMainChallenge.classes DaggerActualRigidificationQuillen.modelD.{u} ∧
    DaggerActualModelChallenge.generationStatement.{u} ∧
    DaggerActualLeftProperChallenge.leftProperStatement.{u} ∧
    DaggerActualModelMainChallenge.trivialFibrationsStatement
      DaggerActualRigidificationQuillen.modelD.{u}

/-- The same standard dagger Joyal model and original adjunction must satisfy all of Theorem B. -/
def statement : Prop :=
  modelStatement.{u} ∧ DaggerActualRigidificationQuillen.adjunction.{u}.IsQuillenEquivalence

end
end DaggerActualMainTheoremBChallenge
