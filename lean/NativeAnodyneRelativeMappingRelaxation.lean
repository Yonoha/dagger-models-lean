import NativePushoutConstantMappingFibres
import NativeAnodyneMappingRestriction
import NativeWeakSquareNativeFibres
import OriginalSimplicialPiZeroWeakEquivalence

/-! Relaxing a fixed subspace along an actual anodyne inclusion is weak on mapping fibres. -/
set_option autoImplicit false
open CategoryTheory MonoidalClosed Simplicial HomotopicalAlgebra
open DaggerNativePushoutConstantMappingFibres DaggerNativeAnodyneMappingRestriction
open DaggerNativeWeakSquareNativeFibres DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeAnodyneRelativeMappingRelaxation
noncomputable section

def relaxationMap {A H D : SSet.{u}} (a : A ⟶ H) (j : H ⟶ D)
    (X : SSet.{u}) (x : X _⦋0⦌) :
    (constantMappingFibre j X x : SSet.{u}) ⟶
      (constantMappingFibre (a ≫ j) X x : SSet.{u}) :=
  SSet.Subcomplex.mapFiber ((MonoidalClosed.pre j).app X)
    ((MonoidalClosed.pre (a ≫ j)).app X) (𝟙 _) ((MonoidalClosed.pre a).app X)
    (by rw [Category.id_comp, MonoidalClosed.pre_map, NatTrans.comp_app])
    _ _ (constant_restriction_vertex a X x)

theorem relaxationMap_ι {A H D : SSet.{u}} (a : A ⟶ H) (j : H ⟶ D)
    (X : SSet.{u}) (x : X _⦋0⦌) :
    relaxationMap a j X x ≫ (constantMappingFibre (a ≫ j) X x).ι =
      (constantMappingFibre j X x).ι := by
  rw [relaxationMap, SSet.Subcomplex.mapFiber_ι, Category.comp_id]

theorem relaxationMap_weak {A H D : SSet.{u}} (a : A ⟶ H) (j : H ⟶ D)
    [Mono a] [Mono j] (ha : SSet.anodyneExtensions a) (X : SSet.{u}) [IsFibrant X]
    (x : X _⦋0⦌) : WeakEquivalence (relaxationMap a j X x) := by
  have : WeakEquivalence ((MonoidalClosed.pre a).app X) :=
    (mem_trivialFibrations_iff _).mp (anodyne_restriction_trivialFibration a ha X) |>.2
  unfold relaxationMap
  exact native_mapFiber_weak _ _ _ _ _ _ _ _

theorem relaxationMap_components_bijective {A H D : SSet.{u}} (a : A ⟶ H) (j : H ⟶ D)
    [Mono a] [Mono j] (ha : SSet.anodyneExtensions a) (X : SSet.{u}) [IsFibrant X]
    (x : X _⦋0⦌) : Function.Bijective (SSet.mapπ₀ (relaxationMap a j X x)) := by
  have := relaxationMap_weak a j ha X x
  exact bijective_mapPiZero _

end
end DaggerNativeAnodyneRelativeMappingRelaxation
