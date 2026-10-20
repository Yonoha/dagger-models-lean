import FixedGraphGenerators
import Mathlib.CategoryTheory.Sums.Products
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-! Structural recognition inputs on the original fixed-object dagger graph category.
Only existing full equivalences and the original homwise geometric W are used.
No graph model structure or cell-closure theorem is assumed or constructed. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerFixedGraph DaggerFixedGraphPlacements DaggerFixedGraphGenerators
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerFixedGraphStructural

noncomputable section

variable (O : Type u)

abbrev DiagramIndex := Discrete (UpperIndex O) ⊕ (Discrete O × DaggerFreeBC2.BC2)

/-- Existing full equivalences supply the missing outer-product (co)limit bridge. -/
def parameterEquivalence : ChosenFunctorParameters O ≌ (DiagramIndex O ⥤ SSet.{u}) :=
  ((piEquivalenceFunctorDiscrete (UpperIndex O) SSet.{u}).prod
    ((piEquivalenceFunctorDiscrete O (DaggerFreeBC2.BC2 ⥤ SSet.{u})).trans
      (CategoryTheory.Functor.currying (C := Discrete O) (D := DaggerFreeBC2.BC2)
        (E := SSet.{u})))).trans
    (CategoryTheory.Sum.functorEquiv (Discrete (UpperIndex O))
      (Discrete O × DaggerFreeBC2.BC2) SSet.{u}).symm

def structuralEquivalence : FixedDaggerSimplicialGraph O ≌
    (DiagramIndex O ⥤ SSet.{u}) :=
  (fixedObjectDecomposition O).trans (parameterEquivalence O)

instance graphLimits : HasLimitsOfSize.{u, u} (FixedDaggerSimplicialGraph O) :=
  Adjunction.has_limits_of_equivalence (structuralEquivalence O).functor

instance graphColimits : HasColimitsOfSize.{u, u} (FixedDaggerSimplicialGraph O) :=
  Adjunction.has_colimits_of_equivalence (structuralEquivalence O).functor

instance graphFiniteLimits : HasFiniteLimits (FixedDaggerSimplicialGraph O) :=
  hasFiniteLimits_of_hasLimitsOfSize _

instance graphLocallySmall : LocallySmall.{u} (FixedDaggerSimplicialGraph O) :=
  CategoryTheory.locallySmall_self _

/-- The original W is tested by inverse image under each literal original homEval. -/
theorem W_iff_coordinates {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    W O f ↔ ∀ x y : O,
      ((weakEquivalences SSet.{u}).inverseImage (homEval O x y)) f := by
  simp only [W, HomotopicalAlgebra.weakEquivalence_iff, MorphismProperty.inverseImage_iff]
  rfl

instance W_twoOutOfThree : (W O).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := by
    rw [W_iff_coordinates] at hf hg ⊢
    intro x y
    exact MorphismProperty.comp_mem _ f g (hf x y) (hg x y)
  of_postcomp f g hg hfg := by
    rw [W_iff_coordinates] at hg hfg ⊢
    intro x y
    exact MorphismProperty.of_postcomp _ f g (hg x y) (hfg x y)
  of_precomp f g hf hfg := by
    rw [W_iff_coordinates] at hf hfg ⊢
    intro x y
    exact MorphismProperty.of_precomp _ f g (hf x y) (hfg x y)

instance W_retracts : (W O).IsStableUnderRetracts where
  of_retract h hg := by
    rw [W_iff_coordinates] at hg ⊢
    intro x y
    exact MorphismProperty.of_retract h (hg x y)

/-- Finite presentability preserves the actual original Nat relative-cell diagram. -/
theorem preservesNatCellColimit (X : FixedDaggerSimplicialGraph O)
    [IsFinitelyPresentable.{u} X] {A B : FixedDaggerSimplicialGraph O} (f : A ⟶ B)
    (hf : RelativeCellComplex.{u} (fun (_ : ℕ) ↦ (I O ⊔ J O).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op X)) := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (coyoneda.obj (Opposite.op X))
  infer_instance

end

end DaggerFixedGraphStructural
