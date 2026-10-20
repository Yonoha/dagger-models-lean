import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Retract
import TopCatModelCategory.CatCommSq

/-!
# Native ordinary-category equivalences as a prospective weak class

Retain the actual Cat morphisms and functors. Reuse native equivalence composition,
cancellation and the existing coherent retract lemma; no model is assumed.
-/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeCatEquivalenceWeakProperties

/-- Equivalence of the actual functor underlying a Cat morphism. -/
def equivalences : MorphismProperty Cat.{u, u} := fun _ _ f ↦ f.toFunctor.IsEquivalence

instance containsIdentities : equivalences.{u}.ContainsIdentities where
  id_mem X := by
    change (𝟭 X).IsEquivalence
    infer_instance

instance stableComposition : equivalences.{u}.IsStableUnderComposition where
  comp_mem f g hf hg := by
    letI : f.toFunctor.IsEquivalence := hf
    letI : g.toFunctor.IsEquivalence := hg
    change (f.toFunctor ⋙ g.toFunctor).IsEquivalence
    infer_instance

instance ofPrecomp : equivalences.{u}.HasOfPrecompProperty equivalences.{u} where
  of_precomp f g hf hfg := by
    letI : f.toFunctor.IsEquivalence := hf
    letI : (f.toFunctor ⋙ g.toFunctor).IsEquivalence := hfg
    exact Functor.isEquivalence_of_comp_left f.toFunctor g.toFunctor

instance ofPostcomp : equivalences.{u}.HasOfPostcompProperty equivalences.{u} where
  of_postcomp f g hg hfg := by
    letI : g.toFunctor.IsEquivalence := hg
    letI : (f.toFunctor ⋙ g.toFunctor).IsEquivalence := hfg
    exact Functor.isEquivalence_of_comp_right f.toFunctor g.toFunctor

instance twoOutOfThree : equivalences.{u}.HasTwoOutOfThreeProperty := ⟨⟩

end DaggerNativeCatEquivalenceWeakProperties
