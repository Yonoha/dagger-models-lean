import OriginalOrdinaryGraphSigmaPresentability
import OriginalOrdinaryFilteredEnrichedColimitComparison
import DaggerModels.OrdinaryTwoObjectCell
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Finite presentability of the original ordinary two-object cell

The original cell's complete Hom equivalence is natural in the target
simplicial category. The ordinary graph sigma functor records both chosen
endpoints, including for an empty or disconnected generating simplicial set.
Its finite accessibility and filtered-colimit preservation by graph forgetting
give finite presentability of the actual ordinary cell.
-/

open CategoryTheory Limits Opposite

universe u

namespace DaggerModels.OrdinaryTwoObjectCell

noncomputable section

open OriginalOrdinaryGraphSigmaFunctor

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Original cell maps are naturally the complete endpoint-indexed graph data. -/
def graphHomIso (K : SSet.{u}) :
    coyoneda.obj (op (cell K)) ≅
      SimplicialCat.graphForget ⋙ sigmaFunctor K :=
  NatIso.ofComponents (fun C ↦ (homEquiv K C).toIso) (by
    intro C D F
    funext m
    change homEquiv K D (m ≫ F) = postData F (homEquiv K C m)
    exact homEquiv_naturality_right m F)

/-- A finitely presentable generating simplicial set gives a finitely
presentable original ordinary two-object cell. -/
theorem cell_isFinitelyPresentable (K : SSet.{u}) [IsFinitelyPresentable.{u} K] :
    IsFinitelyPresentable.{u} (cell K) := by
  letI : (sigmaFunctor K).IsCardinalAccessible Cardinal.aleph0.{u} :=
    sigmaFunctor_isCardinalAccessible K
  letI : SimplicialCat.graphForget.{u}.IsCardinalAccessible Cardinal.aleph0.{u} :=
    (Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize).2 inferInstance
  letI : (SimplicialCat.graphForget ⋙ sigmaFunctor K).IsCardinalAccessible
      Cardinal.aleph0.{u} := inferInstance
  exact Functor.isCardinalAccessible_of_natIso (graphHomIso K).symm Cardinal.aleph0

/-- Every finite simplicial set, including an empty or disconnected one,
gives a finitely presentable original ordinary two-object cell. -/
theorem cell_finite_isFinitelyPresentable (K : SSet.{u}) [K.Finite] :
    IsFinitelyPresentable.{u} (cell K) :=
  cell_isFinitelyPresentable K

/-- In particular, the actual ordinary horn-cell domains are finitely
presentable at the same universe. -/
theorem horn_cell_isFinitelyPresentable (n : ℕ) (i : Fin (n + 1)) :
    IsFinitelyPresentable.{u} (cell (SSet.horn.{u} n i)) :=
  cell_finite_isFinitelyPresentable _

end

end DaggerModels.OrdinaryTwoObjectCell
