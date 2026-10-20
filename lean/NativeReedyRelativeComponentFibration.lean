import NativeReedyRelativeReplacement
import NativeRowwiseWeakEvaluation

/-! Both exact relative-Reedy units identify the original and replaced component arrows. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedyRelativeReplacement
open DaggerNativeRowwiseWeakEvaluation
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyRelativeComponentFibration
noncomputable section

theorem component_unit_square (f : Arrow BiSSet.{u}) :
    componentMap (totalUnit f) ≫ componentMap (relativeReplacement.obj f).hom =
      componentMap f.hom ≫ componentMap (baseUnit f) := by
  apply NatTrans.ext
  funext h q
  change SSet.mapπ₀ ((relativeReplacement.obj f).hom.app h)
    (SSet.mapπ₀ ((totalUnit f).app h) q) =
      SSet.mapπ₀ ((baseUnit f).app h) (SSet.mapπ₀ (f.hom.app h) q)
  rw [← SSet.mapπ₀_comp_apply, ← SSet.mapπ₀_comp_apply]
  exact congrArg (fun k ↦ SSet.mapπ₀ k q) (NatTrans.congr_app (unit_square f) h)

def componentArrowIso (f : Arrow BiSSet.{u}) :
    Arrow.mk (componentMap f.hom) ≅
      Arrow.mk (componentMap (relativeReplacement.obj f).hom) := by
  have hE : ∀ h, WeakEquivalence ((totalUnit f).app h) := fun h ↦
    ((mem_trivialCofibrations_iff _).mp (totalUnit_row_trivial f h)).2
  have hB : ∀ h, WeakEquivalence ((baseUnit f).app h) := fun h ↦
    ((mem_trivialCofibrations_iff _).mp (baseUnit_row_trivial f h)).2
  have := componentMap_isIso (totalUnit f) hE
  have := componentMap_isIso (baseUnit f) hB
  exact Arrow.isoMk (asIso (componentMap (totalUnit f)))
    (asIso (componentMap (baseUnit f))) (component_unit_square f)

theorem component_fibration_iff (f : Arrow BiSSet.{u}) :
    Fibration (C := SSet.{u}) (componentMap f.hom) ↔
      Fibration (C := SSet.{u}) (componentMap (relativeReplacement.obj f).hom) :=
  (fibration_iff _).trans
    (((fibrations SSet.{u}).arrow_mk_iso_iff (componentArrowIso f)).trans
      (fibration_iff _).symm)

end
end DaggerNativeReedyRelativeComponentFibration
