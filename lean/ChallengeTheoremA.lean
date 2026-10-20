import ChallengeActualGlobalModel

/-! This A statement imports project definitions and is not a self-contained
Mathlib-only Comparator Challenge. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerTheoremAChallenge

abbrev G := DaggerActualGlobalModelChallenge.G.{u}
abbrev I : MorphismProperty G.{u} := DaggerActualGlobalModelChallenge.generators.{u}
abbrev J : MorphismProperty G.{u} := DaggerActualGlobalModelChallenge.acyclic.{u}
abbrev W : MorphismProperty G.{u} := DaggerActualGlobalModelChallenge.weak.{u}

/-- All three original classes belong to one and the same model structure. -/
def classes (M : ModelCategory G.{u}) : Prop :=
  M.categoryWithWeakEquivalences.weakEquivalences = W ∧
    M.categoryWithCofibrations.cofibrations = I.rlp.llp ∧
    M.categoryWithFibrations.fibrations = J.rlp

/-- The manuscript's surjective-on-objects, locally trivial Kan condition. -/
def trivialFibrations (M : ModelCategory G.{u}) : Prop :=
  ∀ {C D : G.{u}} (p : C ⟶ D),
    (M.categoryWithFibrations.fibrations ⊓
      M.categoryWithWeakEquivalences.weakEquivalences) p ↔
      Function.Surjective p.obj ∧
        ∀ (x y : C.Obj),
          Fibration (p.map x y) ∧
            SSet.KanComplex.W
              (TopCat.toSSet.map (SSet.toTop.map (p.map x y)))

/-- Pushouts of W along the original I-cofibrations stay in W. -/
def leftProper : Prop :=
  ∀ {C C' B B' : G.{u}}
    {f : C ⟶ C'} {i : C ⟶ B} {j : C' ⟶ B'} {f' : B ⟶ B'},
    IsPushout f i j f' → I.rlp.llp i → W f → W f'

/-- Manuscript Theorem A, including combinatoriality and the trivial-fibration clause. -/
def statement : Prop :=
  ∃ M : ModelCategory G.{u},
    classes M ∧
      DaggerActualGlobalModelChallenge.finiteGenerationStatement.{u} ∧
      trivialFibrations M ∧ leftProper.{u}

end DaggerTheoremAChallenge
