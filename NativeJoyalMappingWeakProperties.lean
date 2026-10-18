import NativeJoyalMappingTest
import NativeCatEquivalenceRetracts

/-!
# Exact ordinary Joyal mapping weak-class identities, composition and retracts

Represent native ho of actual internal Hom precomposition as a contravariant
functor. Pull back the existing ordinary category-equivalence properties. The
weak class is exactly the previously fixed Joyal definition, without a model
assumption or a different weak predicate.
-/
set_option autoImplicit false
open CategoryTheory Opposite
universe u
namespace DaggerNativeJoyalMappingWeakProperties
open DaggerNativeJoyalMappingTest
open DaggerNativeCatEquivalenceWeakProperties

/-- The whole actual native mapping-category assignment, contravariant in its source. -/
def mappingHo (Z : SSet.{u}) : SSet.{u}ᵒᵖ ⥤ Cat.{u, u} where
  obj A := SSet.hoFunctor.obj ((ihom A.unop).obj Z)
  map f := SSet.hoFunctor.map ((MonoidalClosed.pre f.unop).app Z)
  map_id A := by
    change SSet.hoFunctor.map ((MonoidalClosed.pre (𝟙 A.unop)).app Z) = _
    rw [MonoidalClosed.pre_id, NatTrans.id_app, SSet.hoFunctor.map_id]
  map_comp f g := by
    change SSet.hoFunctor.map ((MonoidalClosed.pre (g.unop ≫ f.unop)).app Z) = _
    rw [MonoidalClosed.pre_map, NatTrans.comp_app, SSet.hoFunctor.map_comp]

/-- One literal target test as a native inverse image, retaining the contravariance. -/
def targetTest (Z : SSet.{u}) : MorphismProperty SSet.{u} :=
  (equivalences.inverseImage (mappingHo Z)).unop

instance targetContainsIdentities (Z : SSet.{u}) : (targetTest Z).ContainsIdentities := by
  unfold targetTest
  infer_instance

instance targetTwoOutOfThree (Z : SSet.{u}) : (targetTest Z).HasTwoOutOfThreeProperty := by
  unfold targetTest
  infer_instance

instance targetStableRetracts (Z : SSet.{u}) : (targetTest Z).IsStableUnderRetracts := by
  unfold targetTest
  infer_instance

/-- Exactly the original weak test, not an implication into a substitute class. -/
theorem weak_iff_all_targetTests {A B : SSet.{u}} (f : A ⟶ B) :
    weakCategoricalEquivalences f ↔
      ∀ (Z : SSet.{u}) [SSet.Quasicategory Z], targetTest Z f := Iff.rfl

instance containsIdentities : weakCategoricalEquivalences.{u}.ContainsIdentities where
  id_mem A := by
    intro Z hZ
    exact (targetTest Z).id_mem A

instance stableComposition : weakCategoricalEquivalences.{u}.IsStableUnderComposition where
  comp_mem f g hf hg := by
    intro Z hZ
    exact (targetTest Z).comp_mem f g (hf Z) (hg Z)

instance ofPrecomp :
    weakCategoricalEquivalences.{u}.HasOfPrecompProperty weakCategoricalEquivalences.{u} where
  of_precomp f g hf hfg := by
    intro Z hZ
    exact (targetTest Z).of_precomp (W' := targetTest Z) f g (hf Z) (hfg Z)

instance ofPostcomp :
    weakCategoricalEquivalences.{u}.HasOfPostcompProperty weakCategoricalEquivalences.{u} where
  of_postcomp f g hg hfg := by
    intro Z hZ
    exact (targetTest Z).of_postcomp (W' := targetTest Z) f g (hg Z) (hfg Z)

instance twoOutOfThree : weakCategoricalEquivalences.{u}.HasTwoOutOfThreeProperty := ⟨⟩

instance stableRetracts : weakCategoricalEquivalences.{u}.IsStableUnderRetracts where
  of_retract h hg := by
    intro Z hZ
    exact (targetTest Z).of_retract h (hg Z)

end DaggerNativeJoyalMappingWeakProperties
