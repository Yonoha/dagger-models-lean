import NativeInternalHomCoproductTensorComparison
import NativeHoTensorEquivalence
import NativeJoyalMappingOpposite

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory
open DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeJoyalMappingCoproduct

/-- Binary coproducts preserve the fixed original Joyal mapping weak predicate. -/
theorem weak_coprod_map {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B')
    (hf : weakCategoricalEquivalences f) (hg : weakCategoricalEquivalences g) :
    weakCategoricalEquivalences (coprod.map f g) := by
  intro Z hZ
  exact (DaggerNativeHoEquivalenceIsoSquare.ho_equivalence_iff_of_iso_square
    ((MonoidalClosed.pre (coprod.map f g)).app Z)
    ((MonoidalClosed.pre f).app Z ⊗ₘ (MonoidalClosed.pre g).app Z)
    (DaggerNativeInternalHomCoproductTensorComparison.comparisonIso A' B' Z)
    (DaggerNativeInternalHomCoproductTensorComparison.comparisonIso A B Z)
    (DaggerNativeInternalHomCoproductTensorComparison.pre_naturality f g Z)).2
      (DaggerNativeHoTensorEquivalence.ho_tensor_isEquivalence _ _ (hf Z) (hg Z))

/-- The exact ordinary free-pair underlying map preserves original Joyal mapping weakness. -/
theorem weak_coprod_op_map {A B : SSet.{u}} (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) :
    weakCategoricalEquivalences (coprod.map f (SSet.opFunctor.map f)) :=
  weak_coprod_map f (SSet.opFunctor.map f) hf
    ((DaggerNativeJoyalMappingOpposite.weak_op_iff f).2 hf)

end DaggerNativeJoyalMappingCoproduct
