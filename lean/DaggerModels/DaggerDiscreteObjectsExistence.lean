import DaggerModels.DaggerDiscreteObjects

/-! Closed object-generator existence from the actual discrete constructions.
This protects the initial/terminal notation and the object-lifting step of
Part I `bg.lem.I-inj`, without a Kan or model-category premise. -/

open CategoryTheory Limits

universe u

namespace DaggerModels

/-- Actual initial and terminal dagger categories detect object surjectivity by lifting. -/
theorem exists_daggerObjectGenerator :
    ∃ (E T : DaggerSimplicialCat.{u, u}) (j : E ⟶ T),
      Nonempty (IsInitial E) ∧ Nonempty (IsTerminal T) ∧
      (∀ (C D : DaggerSimplicialCat.{u, u}) (p : C ⟶ D),
        HasLiftingProperty j p ↔ Function.Surjective p.obj) := by
  refine ⟨DaggerDiscreteObjects.empty, DaggerDiscreteObjects.point,
    DaggerDiscreteObjects.emptyToPoint, ⟨DaggerDiscreteObjects.emptyIsInitial⟩,
    ⟨DaggerDiscreteObjects.pointIsTerminal⟩, ?_⟩
  intro C D p
  exact DaggerDiscreteObjects.hasLiftingProperty_iff_surjective p

end DaggerModels
