import DaggerModels.SmallObjectFiniteDomains
import DaggerModels.DaggerGeneratingCofibrations
import DaggerModels.TwoObjectCellPresentability
import DaggerModels.DaggerSimplicialPresentable

/-! The small object argument for the actual I† of Part I `bg.def.IJ`.
Only boundary cells and the object generator occur here. The resulting actual
functorial factorization has classes I†.rlp.llp and I†.rlp; no model structure or
weak-equivalence characterization is asserted. -/

open CategoryTheory Limits MorphismProperty

universe u

namespace DaggerModels.DaggerSmallObject

open DaggerGeneratingCofibrations

/-- The literal generating family is small relative to the original universe. -/
theorem generators_isSmall : MorphismProperty.IsSmall.{u} generators.{u} := by
  have : MorphismProperty.IsSmall.{u} boundaryGenerators.{u} := by
    dsimp [boundaryGenerators]
    infer_instance
  have : MorphismProperty.IsSmall.{u} objectGenerators.{u} := by
    dsimp [objectGenerators]
    infer_instance
  exact SmallObjectFiniteDomains.isSmall_sup boundaryGenerators objectGenerators

/-- Every literal I† domain is finitely presentable, including the empty object generator. -/
theorem generators_domain_isFinitelyPresentable {A B : DaggerSimplicialCat.{u, u}}
    (i : A ⟶ B) (hi : generators i) : IsFinitelyPresentable.{u} A := by
  change boundaryGenerators i ∨ objectGenerators i at hi
  rcases hi with hi | hi
  · cases hi with
    | mk n =>
      exact TwoObjectDaggerCell.cell_finite_isFinitelyPresentable (SSet.boundary n : SSet)
  · cases hi with
    | mk _ =>
      exact SmallObjectFiniteDomains.initial_isFinitelyPresentable
        DaggerDiscreteObjects.emptyIsInitial

/-- The actual I† permits the small object argument with no extra hypotheses. -/
theorem generators_hasSmallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u} generators.{u} := by
  have : HasColimitsOfSize.{u, u} DaggerSimplicialCat.{u, u} := daggerSimplicialCatHasColimits
  have := generators_isSmall.{u}
  exact SmallObjectFiniteDomains.hasSmallObjectArgument.{u} generators
    generators_domain_isFinitelyPresentable

/-- All actual dagger simplicial functors factor functorially in the two stated lifting classes. -/
theorem generators_hasFunctorialFactorization :
    MorphismProperty.HasFunctorialFactorization generators.{u}.rlp.llp generators.rlp := by
  have := generators_hasSmallObjectArgument.{u}
  infer_instance

/-- Actual functorial factorization data, obtained from the proved small object argument. -/
noncomputable def generators_functorialFactorizationData :
    MorphismProperty.FunctorialFactorizationData generators.{u}.rlp.llp generators.rlp := by
  letI := generators_hasFunctorialFactorization.{u}
  exact MorphismProperty.functorialFactorizationData _ _

/-- Each morphism has the factorization induced by the same functorial data. -/
noncomputable def generators_mapFactorizationData {A B : DaggerSimplicialCat.{u, u}}
    (f : A ⟶ B) : MorphismProperty.MapFactorizationData generators.rlp.llp generators.rlp f :=
  generators_functorialFactorizationData.factorizationData f

end DaggerModels.DaggerSmallObject
