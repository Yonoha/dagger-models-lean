import DaggerModels.DaggerSemanticColimit
import DaggerModels.DaggerFiniteGenerators
import DaggerModels.DaggerSimplicialLimits

/-! Local finite presentability of the actual dagger simplicial
category. The colimit premise of the generator criterion is discharged by
the constructed semantic quotient colimits. This does not prove the separate
ordinary-category forgetful creation statement or any model structure. -/

open CategoryTheory Limits

universe u

namespace DaggerModels

theorem daggerSimplicialCatHasLimits : HasLimits DaggerSimplicialCat.{u, u} :=
  DaggerSimplicialCat.daggerSimplicialHasLimits

theorem daggerSimplicialCatHasColimits : HasColimits DaggerSimplicialCat.{u, u} :=
  DaggerSimplicialCat.SemanticColimit.daggerSimplicialCatHasColimits

/-- The complete local finite presentability assertion of Part I `bg.lem.presentable`. -/
theorem daggerSimplicialCatLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} DaggerSimplicialCat.{u, u} := by
  letI : HasColimits DaggerSimplicialCat.{u, u} := daggerSimplicialCatHasColimits
  exact DaggerSimplicialCat.locallyFinitelyPresentable_of_hasColimits

theorem daggerSimplicialCatLocallyPresentable :
    IsLocallyPresentable.{u} DaggerSimplicialCat.{u, u} := by
  letI : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact ⟨Cardinal.aleph0, inferInstance, daggerSimplicialCatLocallyFinitelyPresentable⟩

end DaggerModels
