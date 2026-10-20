import OriginalOrdinaryTerminal
import OriginalOrdinaryHornObjectBijections
import OriginalOrdinaryLocalFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Functorial original ordinary local Kan construction

One chosen functorial small-object factorization of the diagram of terminal
arrows defines a functor on original simplicial categories. Its unit is
bijective on objects and its output has Kan Hom simplicial sets. No Hom
weak-equivalence or model-structure assertion is made.
-/

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
  MonoidalCategory CartesianMonoidalCategory SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OriginalOrdinaryLocalKanReplacement

open OriginalOrdinaryHornGenerators

noncomputable section

/-- A single choice of the actual functorial horn-cell factorization. -/
def factorizationData : MorphismProperty.FunctorialFactorizationData
    generators.{u}.rlp.llp generators.rlp := by
  letI := generators_hasFunctorialFactorization.{u}
  exact MorphismProperty.functorialFactorizationData _ _

/-- The chosen middle-object functor on the diagram of terminal arrows. -/
def replacement : SimplicialCat.{u, u} ⥤ SimplicialCat.{u, u} :=
  OriginalOrdinaryTerminal.terminalArrow ⋙ factorizationData.Z

/-- The constant functor at the concrete terminal ordinary simplicial category. -/
def terminalConstant : SimplicialCat.{u, u} ⥤ SimplicialCat.{u, u} :=
  (Functor.const SimplicialCat.{u, u}).obj OriginalOrdinaryTerminal.terminal

/-- The natural left factor of every original terminal map. -/
def unit : 𝟭 SimplicialCat.{u, u} ⟶ replacement where
  app C := factorizationData.i.app (OriginalOrdinaryTerminal.terminalArrow.obj C)
  naturality {C D} F := by
    change F ≫ factorizationData.i.app
        (OriginalOrdinaryTerminal.terminalArrow.obj D) =
      factorizationData.i.app (OriginalOrdinaryTerminal.terminalArrow.obj C) ≫
        factorizationData.Z.map (OriginalOrdinaryTerminal.terminalArrow.map F)
    exact factorizationData.i.naturality (OriginalOrdinaryTerminal.terminalArrow.map F)

/-- The natural right factor into the concrete terminal object. -/
def projection : replacement ⟶ terminalConstant where
  app C := factorizationData.p.app (OriginalOrdinaryTerminal.terminalArrow.obj C)
  naturality {C D} F := by
    change factorizationData.Z.map (OriginalOrdinaryTerminal.terminalArrow.map F) ≫
        factorizationData.p.app (OriginalOrdinaryTerminal.terminalArrow.obj D) =
      factorizationData.p.app (OriginalOrdinaryTerminal.terminalArrow.obj C) ≫
        𝟙 OriginalOrdinaryTerminal.terminal
    exact factorizationData.p.naturality (OriginalOrdinaryTerminal.terminalArrow.map F)

/-- The natural factors compose to the actual map to the concrete terminal. -/
theorem fac_point (C : SimplicialCat.{u, u}) :
    unit.app C ≫ projection.app C = OriginalOrdinaryTerminal.terminalMap C :=
  factorizationData.fac_app (f := OriginalOrdinaryTerminal.terminalArrow.obj C)

/-- Every component of the unit belongs to the actual horn-cell left class. -/
theorem unit_left (C : SimplicialCat.{u, u}) :
    generators.rlp.llp (unit.app C) :=
  factorizationData.hi (OriginalOrdinaryTerminal.terminalArrow.obj C)

/-- Every component of the projection belongs to the actual horn-cell right class. -/
theorem projection_right (C : SimplicialCat.{u, u}) :
    generators.rlp (projection.app C) :=
  factorizationData.hp (OriginalOrdinaryTerminal.terminalArrow.obj C)

/-- The unit is bijective on the original objects, without identifying their types. -/
theorem unit_obj_bijective (C : SimplicialCat.{u, u}) :
    Function.Bijective (unit.app C).obj :=
  OriginalOrdinaryHornObjectBijections.object_bijective_of_generators_rlp_llp
    (unit.app C) (unit_left C)

/-- Every Hom simplicial set of the functorial output is a Kan complex. -/
theorem replacement_locallyKan (C : SimplicialCat.{u, u})
    (x y : (replacement.obj C).Obj) :
    SSet.KanComplex (x ⟶[SSet.{u}] y) := by
  have hF : Fibration ((projection.app C).map x y) :=
    (OriginalOrdinaryLocalFibrations.generators_rlp_iff (projection.app C)).1
      (projection_right C) x y
  have hT : IsTerminal
      ((projection.app C).obj x ⟶[SSet.{u}] (projection.app C).obj y) := by
    change IsTerminal (𝟙_ SSet.{u})
    exact isTerminalTensorUnit
  letI : (fibrations SSet.{u}).RespectsIso := by
    rw [fibrations_eq]
    infer_instance
  exact (isFibrant_iff_of_isTerminal ((projection.app C).map x y) hT).2 hF

end

end DaggerModels.OriginalOrdinaryLocalKanReplacement
