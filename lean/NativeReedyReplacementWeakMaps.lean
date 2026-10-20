import NativeReedyRelativeReplacement

/-! The actual Reedy replacements preserve weak maps in every original row. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyReplacementWeakMaps
noncomputable section

theorem replacement_map_row_weak {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : ∀ h, WeakEquivalence (f.app h)) (h : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((DaggerNativeFunctorialReedyReplacement.replacement.map f).app h) := by
  have := hf h
  have := DaggerNativeFunctorialReedyReplacement.unit_row_weak X h
  have := DaggerNativeFunctorialReedyReplacement.unit_row_weak Y h
  have he : (DaggerNativeFunctorialReedyReplacement.unit.app X).app h ≫
      (DaggerNativeFunctorialReedyReplacement.replacement.map f).app h =
      f.app h ≫ (DaggerNativeFunctorialReedyReplacement.unit.app Y).app h :=
    NatTrans.congr_app (DaggerNativeFunctorialReedyReplacement.unit.naturality f).symm h
  exact weakEquivalence_of_precomp_of_fac he

theorem relative_total_map_row_weak {f g : Arrow BiSSet.{u}} (s : f ⟶ g)
    (hs : ∀ h, WeakEquivalence (s.left.app h)) (h : SimplexCategoryᵒᵖ) :
    WeakEquivalence
      ((DaggerNativeReedyRelativeReplacement.relativeReplacement.map s).left.app h) := by
  have := hs h
  have : WeakEquivalence ((DaggerNativeReedyRelativeReplacement.totalUnit f).app h) :=
    ((mem_trivialCofibrations_iff _).mp
      (DaggerNativeReedyRelativeReplacement.totalUnit_row_trivial f h)).2
  have : WeakEquivalence ((DaggerNativeReedyRelativeReplacement.totalUnit g).app h) :=
    ((mem_trivialCofibrations_iff _).mp
      (DaggerNativeReedyRelativeReplacement.totalUnit_row_trivial g h)).2
  have he : (DaggerNativeReedyRelativeReplacement.totalUnit f).app h ≫
      (DaggerNativeReedyRelativeReplacement.relativeReplacement.map s).left.app h =
      s.left.app h ≫ (DaggerNativeReedyRelativeReplacement.totalUnit g).app h :=
    NatTrans.congr_app (DaggerNativeReedyRelativeReplacement.totalUnit_natural s) h
  exact weakEquivalence_of_precomp_of_fac he

theorem relative_base_map_row_weak {f g : Arrow BiSSet.{u}} (s : f ⟶ g)
    (hs : ∀ h, WeakEquivalence (s.right.app h)) (h : SimplexCategoryᵒᵖ) :
    WeakEquivalence
      ((DaggerNativeReedyRelativeReplacement.relativeReplacement.map s).right.app h) :=
  replacement_map_row_weak s.right hs h

end
end DaggerNativeReedyReplacementWeakMaps
