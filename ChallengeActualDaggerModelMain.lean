import ChallengeActualDaggerModel
import ChallengeActualDaggerLeftProper
import TopCatModelCategory.ModelCategorySSet

/-! The model-structure part of Theorem B, with all literal classes and trivial fibrations. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualModelMainChallenge

abbrev D := DaggerSSet.{u}
abbrev weak : MorphismProperty D.{u} := DaggerActualModelChallenge.weak.{u}
abbrev cof : MorphismProperty D.{u} := DaggerActualModelChallenge.cof.{u}

def classes (M : ModelCategory D.{u}) : Prop :=
  M.categoryWithWeakEquivalences.weakEquivalences = weak ∧
    M.categoryWithCofibrations.cofibrations = cof ∧
    M.categoryWithFibrations.fibrations = (cof ⊓ weak).rlp

def ordinaryTrivial {X Y : D.{u}} (p : X ⟶ Y) : Prop :=
  Fibration p.hom ∧
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map p.hom))

def trivialFibrationsStatement (M : ModelCategory D.{u}) : Prop :=
  ∀ {X Y : D.{u}} (p : X ⟶ Y),
    (M.categoryWithFibrations.fibrations ⊓ M.categoryWithWeakEquivalences.weakEquivalences) p ↔
      ordinaryTrivial p

def statement : Prop :=
  ∃ M : ModelCategory D.{u}, classes M ∧
    DaggerActualModelChallenge.generationStatement.{u} ∧
    DaggerActualLeftProperChallenge.leftProperStatement.{u} ∧ trivialFibrationsStatement M

end DaggerActualModelMainChallenge
