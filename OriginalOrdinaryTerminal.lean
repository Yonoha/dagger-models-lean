import DaggerModels.SimplicialObjectAdjunctions
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# A concrete terminal object in the original ordinary simplicial categories

The codiscrete category on one object has the actual tensor-unit simplicial
set as every Hom. Its unique incoming enriched functor is assembled into a
functorial terminal-arrow diagram for subsequent small-object factorization.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace DaggerModels.OriginalOrdinaryTerminal

noncomputable section

/-- The original codiscrete simplicial category on a singleton object type. -/
def terminal : SimplicialCat.{u, u} :=
  SimplicialCat.codiscrete (PUnit : Type u)

/-- The literal constant-object enriched functor to the concrete terminal object. -/
def terminalMap (C : SimplicialCat.{u, u}) : C ⟶ terminal :=
  SimplicialCat.codiscreteLift C (fun _ ↦ PUnit.unit)

@[simp]
theorem terminalMap_obj (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (terminalMap C).obj x = PUnit.unit := rfl

/-- On every original Hom, the terminal map is the canonical map to the actual
terminal simplicial set. -/
theorem terminalMap_map (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    (terminalMap C).map x y =
      (isTerminalTensorUnit.from (x ⟶[SSet.{u}] y) :
        (x ⟶[SSet.{u}] y) ⟶ 𝟙_ SSet.{u}) := rfl

/-- Uniqueness follows from the original codiscrete Hom equivalence. -/
theorem terminalMap_unique {C : SimplicialCat.{u, u}} (F : C ⟶ terminal) :
    F = terminalMap C := by
  apply (SimplicialCat.codiscreteHomEquiv C (PUnit : Type u)).symm.injective
  funext x
  exact Subsingleton.elim _ _

/-- The concrete original codiscrete one-object category is terminal. -/
def isTerminal : IsTerminal terminal.{u} :=
  IsTerminal.ofUniqueHom terminalMap (fun _ F ↦ terminalMap_unique F)

/-- The chosen map is the canonical projection from terminality. -/
theorem terminalMap_eq_from (C : SimplicialCat.{u, u}) :
    terminalMap C = isTerminal.from C :=
  isTerminal.hom_ext _ _

/-- The terminal projections commute with every original enriched functor. -/
theorem terminalMap_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    F ≫ terminalMap D = terminalMap C :=
  isTerminal.hom_ext _ _

/-- The functorial diagram of actual terminal projections. -/
def terminalArrow : SimplicialCat.{u, u} ⥤ Arrow SimplicialCat.{u, u} where
  obj C := Arrow.mk (terminalMap C)
  map F := Arrow.homMk' F (𝟙 terminal) (by
    simpa only [Category.comp_id] using terminalMap_naturality F)
  map_id C := by
    apply Arrow.hom_ext
    · rfl
    · rfl
  map_comp F G := by
    apply Arrow.hom_ext
    · rfl
    · rfl

@[simp]
theorem terminalArrow_obj (C : SimplicialCat.{u, u}) :
    terminalArrow.obj C = Arrow.mk (terminalMap C) := rfl

@[simp]
theorem terminalArrow_map_left {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    (terminalArrow.map F).left = F := rfl

@[simp]
theorem terminalArrow_map_right {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    (terminalArrow.map F).right = 𝟙 terminal := rfl

end

end DaggerModels.OriginalOrdinaryTerminal
