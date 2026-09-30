import DaggerModels.DaggerSplitCoequalizer
import DaggerModels.DaggerGraphCoequalizer
import DaggerModels.DaggerGraphReflection
import DaggerModels.FreeDaggerSimplicialCategory
import Mathlib.CategoryTheory.Monad.Monadicity

/-!
# Monadicity of dagger simplicial categories over dagger graphs

This proves the first assertion of Part I `bg.lem.presentable` for the actual
graph forgetful functor. The split quotient enrichment, quotient functor and
coequalizer universal property are constructed before applying Beck's theorem.
Local finite presentability additionally requires the finitary word monad and
presentability of dagger simplicial graphs; it is not asserted in this module.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace DaggerModels.DaggerSimplicialCat

namespace SplitCoequalizer

variable {A B : DaggerSimplicialCat.{u, u}} {f g : A ⟶ B}
  {Q : DaggerSimplicialGraph.{u}} {π : underlyingGraph B ⟶ Q}

/-- Copy the actual Mathlib split diagram without changing any of its equations. -/
def GraphSplitData.ofMathlib
    (s : IsSplitCoequalizer (forgetGraph.map f) (forgetGraph.map g) π) :
    GraphSplitData f g π where
  rightSection := s.rightSection
  leftSection := s.leftSection
  condition := s.condition
  rightSection_π := s.rightSection_π
  leftSection_bottom := s.leftSection_bottom
  leftSection_top := s.leftSection_top

/-- The constructed quotient functor coequalizes the original enriched pair. -/
theorem quotient_condition (s : GraphSplitData f g π) :
    f ≫ quotientFunctor s = g ≫ quotientFunctor s := by
  apply forgetGraph.map_injective
  exact s.condition

/-- Forgetting the constructed quotient functor recovers the given split diagram. -/
def quotientGraphSplit (s : GraphSplitData f g π) :
    IsSplitCoequalizer (forgetGraph.map f) (forgetGraph.map g)
      (forgetGraph.map (quotientFunctor s)) where
  rightSection := s.rightSection
  leftSection := s.leftSection
  condition := s.condition
  rightSection_π := s.rightSection_π
  leftSection_bottom := s.leftSection_bottom
  leftSection_top := s.leftSection_top

/-- The enriched quotient is a genuine coequalizer, with no further premise. -/
def quotientIsColimit (s : GraphSplitData f g π) :
    IsColimit (Cofork.ofπ (quotientFunctor s) (quotient_condition s)) :=
  GraphCoequalizer.isColimit (quotientFunctor s) (quotient_condition s) (quotientGraphSplit s)

/-- Take the splitting supplied by Mathlib's actual `IsSplitPair` class. -/
noncomputable def chosenSplitData (f g : A ⟶ B) [forgetGraph.IsSplitPair f g] :
    GraphSplitData f g
      (HasSplitCoequalizer.coequalizerπ (forgetGraph.map f) (forgetGraph.map g)) :=
  GraphSplitData.ofMathlib
    (HasSplitCoequalizer.isSplitCoequalizer (forgetGraph.map f) (forgetGraph.map g))

end SplitCoequalizer

/-- Every graph-split pair has the actual enriched coequalizer constructed above. -/
noncomputable instance forgetGraphHasCoequalizerOfIsSplitPair :
    Monad.HasCoequalizerOfIsSplitPair forgetGraph.{u} where
  out f g :=
    let s := SplitCoequalizer.chosenSplitData f g
    GraphCoequalizer.hasCoequalizer (SplitCoequalizer.quotientFunctor s)
      (SplitCoequalizer.quotient_condition s) (SplitCoequalizer.quotientGraphSplit s)

/-- The original graph forgetful functor preserves coequalizers of graph-split pairs. -/
noncomputable instance forgetGraphPreservesColimitOfIsSplitPair :
    Monad.PreservesColimitOfIsSplitPair forgetGraph.{u} where
  out f g :=
    let s := SplitCoequalizer.chosenSplitData f g
    GraphCoequalizer.preservesColimit (SplitCoequalizer.quotientFunctor s)
      (SplitCoequalizer.quotient_condition s) (SplitCoequalizer.quotientGraphSplit s)

/-- Beck monadicity for the original free finite-path and graph forgetful adjunction. -/
noncomputable instance forgetGraphMonadicRightAdjoint : MonadicRightAdjoint forgetGraph.{u} :=
  Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms
    FreeDaggerSimplicialCategory.adjunction

/-- The monadicity assertion of Part I `bg.lem.presentable`. -/
theorem forgetGraph_monadic : Nonempty (MonadicRightAdjoint forgetGraph.{u}) :=
  ⟨forgetGraphMonadicRightAdjoint⟩

end DaggerModels.DaggerSimplicialCat
