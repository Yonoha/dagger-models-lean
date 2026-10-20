import NativeCoproductReindexedWeak
import OriginalNerveLocalWeakPreservation
import OriginalSimplicialCategoryBarReplacementFibreComparison
import OriginalSimplicialCategoryBarWeakFunctor

/-! The original whole strict/replacement fibre comparison is invariant under local weak maps. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerNativeCoproductReindexedWeak DaggerOriginalNerveLocalWeakPreservation
open DaggerOriginalSimplicialCategoryBarConstruction DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalSimplicialCategoryBarWeakFunctor
open DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
open DaggerOriginalSimplicialCategoryBarReplacementFibreComparison
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalBarLocalWeakComparisonInvariance
noncomputable section

theorem wholeBarMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj) : WeakEquivalence (barMap F) :=
  map'_weak F.obj hO (barComponentMap F) (barComponentMap_weakEquivalence F)

theorem originalHomSumMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (x : C.Obj) :
    WeakEquivalence (originalHomSumMap F x) :=
  map'_weak F.obj hO (F.map x) (hF x)

theorem replacementFibreMap_weak_of_local {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (x : C.Obj) :
    WeakEquivalence (replacementFibreMap F x) :=
  replacementFibreMap_weak F x (wholeBarMap_weak F hO) (diagonalNerveMap_weak F hO hF)

theorem strictComparison_weak_iff {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (x : C.Obj) :
    WeakEquivalence (strictFibreComparison C x) ↔
      WeakEquivalence (strictFibreComparison D (F.obj x)) := by
  have : WeakEquivalence (originalHomSumMap F x) := originalHomSumMap_weak F hO hF x
  have : WeakEquivalence (replacementFibreMap F x) := replacementFibreMap_weak_of_local F hO hF x
  constructor
  · intro hC
    have := hC
    have : WeakEquivalence (strictFibreComparison C x ≫ replacementFibreMap F x) := inferInstance
    exact weakEquivalence_of_precomp_of_fac (strictFibreComparison_natural F x).symm
  · intro hD
    have := hD
    have : WeakEquivalence (originalHomSumMap F x ≫
        strictFibreComparison D (F.obj x)) := inferInstance
    exact weakEquivalence_of_postcomp_of_fac (strictFibreComparison_natural F x)

end
end DaggerOriginalBarLocalWeakComparisonInvariance
