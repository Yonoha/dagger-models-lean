import NativeAmbientDaggerFibrancy
import OriginalSimplicialCotensorRestriction
import OriginalFixedObjectCotensors

/-! Reuse the ORIGINAL cotensor on ALL ambient fixed-object dagger categories.
Native fibrant targets give fibrations for mono parameters and trivial fibrations for anodynes.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectCotensors
open DaggerOriginalSimplicialCotensorRestriction DaggerNativeAmbientDaggerFibrancy
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeAmbientDaggerCotensorFibrations
noncomputable section

theorem restriction_fibration {O : Type u} {K L : SSet.{u}} (j : K ⟶ L) [Mono j]
    (D : FixedDaggerCategory O) [IsFibrant D] : Fibration (daggerCotensorPre j D) := by
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original]
  intro x y
  have := hom_kan D x y
  exact pre_fibration j (D.underlying.enriched.Hom x y)

theorem restriction_trivialFibration {O : Type u} {K L : SSet.{u}} (j : K ⟶ L)
    (hj : SSet.anodyneExtensions j) (D : FixedDaggerCategory O) [IsFibrant D] :
    trivialFibrations (FixedDaggerCategory O) (daggerCotensorPre j D) := by
  rw [mem_trivialFibrations_iff,
    DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original,
    DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original]
  constructor
  · intro x y
    have := hom_kan D x y
    exact ((mem_trivialFibrations_iff _).mp
      (pre_trivialFibration j hj (D.underlying.enriched.Hom x y))).1
  · intro x y
    have := hom_kan D x y
    exact ((mem_trivialFibrations_iff _).mp
      (pre_trivialFibration j hj (D.underlying.enriched.Hom x y))).2

end
end DaggerNativeAmbientDaggerCotensorFibrations
