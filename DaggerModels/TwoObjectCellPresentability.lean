import DaggerModels.TwoObjectDaggerCellUniversal
import DaggerModels.TwoObjectGraphPresentability
import DaggerModels.DaggerSimplicialFilteredColimits
import Mathlib.CategoryTheory.Presentable.Adjunction

/-! The finite compactness assertion following Part I `bg.eq.A-univ`.
The proof retains both endpoints even for empty or disconnected simplicial sets. -/

open CategoryTheory Limits Opposite MonoidalCategory

universe u

namespace DaggerModels.TwoObjectDaggerCell

noncomputable section

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The original graph Hom functor is naturally the complete endpoint-indexed sum. -/
def graphHomIso (K : SSet.{u}) :
    coyoneda.obj (op (TwoObjectDaggerGraph.graph K)) ≅
      TwoObjectGraphPresentability.sigmaFunctor K :=
  NatIso.ofComponents (fun G ↦ (TwoObjectDaggerGraph.homEquiv K G).toIso) (by
    intro G H f
    funext m
    rfl)

/-- A finitely presentable generating simplicial set gives a finitely presentable graph. -/
theorem graph_isFinitelyPresentable (K : SSet.{u}) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} (TwoObjectDaggerGraph.graph K) := by
  letI := TwoObjectGraphPresentability.sigmaFunctor_isCardinalAccessible K
  exact Functor.isCardinalAccessible_of_natIso (graphHomIso K).symm Cardinal.aleph0

/-- The actual free cell is finitely presentable because the graph forgetful functor is finitary. -/
theorem cell_isFinitelyPresentable (K : SSet.{u}) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} (cell K) := by
  letI := graph_isFinitelyPresentable K
  letI := DaggerSimplicialCat.forgetGraphIsCardinalAccessibleAleph0.{u}
  exact FreeDaggerSimplicialCategory.adjunction.isCardinalPresentable_leftAdjoint_obj
    Cardinal.aleph0 (TwoObjectDaggerGraph.graph K)

/-- In particular the manuscript's finite `K` gives a finitely presentable two-object graph. -/
theorem graph_finite_isFinitelyPresentable (K : SSet.{u}) [K.Finite] :
    IsFinitelyPresentable.{u} (TwoObjectDaggerGraph.graph K) :=
  graph_isFinitelyPresentable K

/-- The finite compactness claim following the two-object universal property. -/
theorem cell_finite_isFinitelyPresentable (K : SSet.{u}) [K.Finite] :
    IsFinitelyPresentable.{u} (cell K) := cell_isFinitelyPresentable K

end
end DaggerModels.TwoObjectDaggerCell

namespace DaggerModels

/-- Finite simplicial sets have actual finitely presentable cells
with the full universal property. -/
theorem exists_finitelyPresentable_twoObjectDaggerCell (K : SSet.{u}) [K.Finite] :
    ∃ (C : DaggerSimplicialCat.{u, u}) (_ : IsFinitelyPresentable.{u} C)
      (x y : C.Obj) (i : K ⟶ (x ⟶[SSet.{u}] y)),
      ∀ D : DaggerSimplicialCat.{u, u},
        Function.Bijective (DaggerSimplicialCat.classifyTwoObjectCell x y i (D := D)) := by
  refine ⟨TwoObjectDaggerCell.cell K, TwoObjectDaggerCell.cell_finite_isFinitelyPresentable K,
    TwoObjectDaggerGraph.left, TwoObjectDaggerGraph.right, TwoObjectDaggerCell.generator K, ?_⟩
  intro D
  exact (TwoObjectDaggerCell.homEquiv K D).bijective

end DaggerModels
