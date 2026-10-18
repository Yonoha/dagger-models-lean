import OriginalOrdinaryCellFinitePresentability
import DaggerModels.SmallObjectFiniteDomains
import DaggerModels.SimplicialColimits
import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# Original ordinary two-object horn generators

This is the literal family of positive-dimensional horn-cell maps in the
original ordinary simplicial-category type. Finite presentability of their
domains gives the small object argument and its generic functorial
factorization. No lifting-class or weak-equivalence characterization is
asserted here.
-/

open CategoryTheory Limits MorphismProperty

universe u

namespace DaggerModels.OriginalOrdinaryHornGenerators

/-- Positive-dimensional horn indices, including both outer horns. -/
abbrev Index := Σ n : ℕ, Fin (n + 2)

/-- The original ordinary two-object cell on an actual horn inclusion. -/
noncomputable def generator (a : Index) :
    OrdinaryTwoObjectCell.cell (SSet.horn.{u} (a.1 + 1) a.2) ⟶
      OrdinaryTwoObjectCell.cell
        (SSet.stdSimplex.obj (SimplexCategory.mk (a.1 + 1))) :=
  OrdinaryTwoObjectCell.functor.map (SSet.horn.{u} (a.1 + 1) a.2).ι

/-- The literal ordinary horn-cell family. -/
def generators : MorphismProperty SimplicialCat.{u, u} :=
  .ofHoms generator

/-- The family is small at the same universe as the simplicial categories. -/
theorem generators_isSmall : MorphismProperty.IsSmall.{u} generators.{u} := by
  dsimp [generators]
  infer_instance

/-- Every individual ordinary horn-cell source is finitely presentable. -/
theorem generatorSource_isFinitelyPresentable (a : Index) :
    IsFinitelyPresentable.{u}
      (OrdinaryTwoObjectCell.cell (SSet.horn.{u} (a.1 + 1) a.2)) :=
  OrdinaryTwoObjectCell.horn_cell_isFinitelyPresentable (a.1 + 1) a.2

/-- Every member of the literal family has a finitely presentable source. -/
theorem generatorsSource_isFinitelyPresentable {A B : SimplicialCat.{u, u}}
    (i : A ⟶ B) (hi : generators i) : IsFinitelyPresentable.{u} A := by
  change MorphismProperty.ofHoms generator i at hi
  cases hi with
  | mk a => exact generatorSource_isFinitelyPresentable a

/-- The actual ordinary horn-cell family satisfies Mathlib's small object argument. -/
theorem generators_hasSmallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u} generators.{u} := by
  have : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
    SimplicialCat.SemanticColimit.simplicialCatHasColimits
  have := generators_isSmall.{u}
  exact SmallObjectFiniteDomains.hasSmallObjectArgument.{u} generators
    generatorsSource_isFinitelyPresentable

/-- The corresponding lifting classes admit a generic functorial factorization. -/
theorem generators_hasFunctorialFactorization :
    MorphismProperty.HasFunctorialFactorization generators.{u}.rlp.llp generators.rlp := by
  have := generators_hasSmallObjectArgument.{u}
  infer_instance

end DaggerModels.OriginalOrdinaryHornGenerators
