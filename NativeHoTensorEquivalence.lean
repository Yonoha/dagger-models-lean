import NativeHoEquivalenceIsoSquare
import NativeInternalHomOppositeComparison

set_option autoImplicit false
open CategoryTheory MonoidalCategory
universe u
namespace DaggerNativeHoTensorEquivalence

/-- Native ho of the actual tensor of two maps preserves both supplied equivalence tests. -/
theorem ho_tensor_isEquivalence {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : (SSet.hoFunctor.map f).toFunctor.IsEquivalence)
    (hg : (SSet.hoFunctor.map g).toFunctor.IsEquivalence) :
    (SSet.hoFunctor.map (f ⊗ₘ g)).toFunctor.IsEquivalence := by
  letI : (SSet.hoFunctor.map f).toFunctor.IsEquivalence := hf
  letI : (SSet.hoFunctor.map g).toFunctor.IsEquivalence := hg
  have hp :
      (SSet.hoFunctor.map f ⊗ₘ SSet.hoFunctor.map g).toFunctor.IsEquivalence :=
    show ((SSet.hoFunctor.map f).toFunctor.asEquivalence.prod
      (SSet.hoFunctor.map g).toFunctor.asEquivalence).functor.IsEquivalence by infer_instance
  exact (DaggerNativeHoEquivalenceIsoSquare.cat_equivalence_iff_of_iso_square
    (SSet.hoFunctor.map (f ⊗ₘ g)) (SSet.hoFunctor.map f ⊗ₘ SSet.hoFunctor.map g)
    (CartesianMonoidalCategory.prodComparisonIso SSet.hoFunctor X Y)
    (CartesianMonoidalCategory.prodComparisonIso SSet.hoFunctor X' Y')
    (CartesianMonoidalCategory.prodComparison_natural SSet.hoFunctor f g)).2 hp

end DaggerNativeHoTensorEquivalence
