import DaggerModels.DaggerSimplicialMonadicity
import DaggerModels.DaggerGraphPresentable
import DaggerModels.FreeWordFinitary
import Mathlib.CategoryTheory.Monad.Limits

/-!
# Filtered colimits of dagger simplicial categories

The proved finitary word composite and monadicity make the original graph
forgetful functor create all small filtered colimits. Those colimits exist
because dagger graphs have them. No finitarity premise remains, and this
module does not assert the existence of all small colimits.
-/

open CategoryTheory Limits

universe u

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace DaggerModels.DaggerSimplicialCat

/-- Beck's actual monadic instance keeps the original finite-word left adjoint. -/
theorem monadicLeftAdjoint_forgetGraph :
    monadicLeftAdjoint forgetGraph.{u} = FreeDaggerSimplicialCategory.functor := rfl

attribute [local instance] FreeWordFinitary.isCardinalAccessible

/-- The actual word monad supplies both preservation hypotheses for monadic creation. -/
noncomputable def forgetGraphCreatesFilteredColimit (J : Type u) [SmallCategory J]
    [IsFiltered J] (K : J ⥤ DaggerSimplicialCat.{u, u}) :
    CreatesColimit K forgetGraph := by
  let : IsCardinalFiltered J Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff J).2 inferInstance
  let : PreservesColimitsOfShape J (FreeDaggerSimplicialCategory.functor ⋙ forgetGraph) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ Cardinal.aleph0 J
  let : PreservesColimitsOfShape J (monadicLeftAdjoint forgetGraph ⋙ forgetGraph) := by
    change PreservesColimitsOfShape J (FreeDaggerSimplicialCategory.functor ⋙ forgetGraph)
    infer_instance
  exact monadicCreatesColimitOfPreservesColimit forgetGraph K

/-- Creation holds for every diagram of any `u`-small filtered shape. -/
noncomputable def forgetGraphCreatesFilteredColimitsOfShape (J : Type u) [SmallCategory J]
    [IsFiltered J] : CreatesColimitsOfShape J forgetGraph.{u} :=
  ⟨fun {K} ↦ forgetGraphCreatesFilteredColimit J K⟩

/-- Filtered diagrams have colimits lifted from their actual underlying graphs. -/
theorem daggerSimplicialCatHasFilteredColimitsOfShape (J : Type u) [SmallCategory J]
    [IsFiltered J] : HasColimitsOfShape J DaggerSimplicialCat.{u, u} := by
  let : HasColimits DaggerSimplicialGraph.{u} := daggerGraphHasColimits
  let : CreatesColimitsOfShape J forgetGraph.{u} :=
    forgetGraphCreatesFilteredColimitsOfShape J
  exact hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape forgetGraph

/-- Creation and graph colimits imply preservation by the original forgetful functor. -/
theorem forgetGraphPreservesFilteredColimitsOfShape (J : Type u) [SmallCategory J]
    [IsFiltered J] : PreservesColimitsOfShape J forgetGraph.{u} := by
  let : HasColimits DaggerSimplicialGraph.{u} := daggerGraphHasColimits
  let : CreatesColimitsOfShape J forgetGraph.{u} :=
    forgetGraphCreatesFilteredColimitsOfShape J
  infer_instance

/-- Finite accessibility of the actual graph forgetful functor. -/
theorem forgetGraphIsCardinalAccessibleAleph0 :
    forgetGraph.{u}.IsCardinalAccessible Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    let : IsFiltered J := (isCardinalFiltered_aleph0_iff J).1 inferInstance
    exact forgetGraphPreservesFilteredColimitsOfShape J

/-- The category has all `u`-small `ℵ₀`-filtered colimits with no additional hypothesis. -/
theorem daggerSimplicialCatHasCardinalFilteredColimitsAleph0 :
    HasCardinalFilteredColimits DaggerSimplicialCat.{u, u} Cardinal.aleph0.{u} where
  hasColimitsOfShape J _ _ := by
    let : IsFiltered J := (isCardinalFiltered_aleph0_iff J).1 inferInstance
    exact daggerSimplicialCatHasFilteredColimitsOfShape J

end DaggerModels.DaggerSimplicialCat
