import NativeReedyReplacementFibres
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! Exact bisimplicial fibre comparisons commute with pullback-preserving functors. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedyRelativeReplacement
open DaggerNativeSSetFibrationSquareFibreWeak
universe u
namespace DaggerNativeRelativeReedyBisimplicialFibres
noncomputable section

def originalBiFibre (f : Arrow BiSSet.{u}) {K : BiSSet.{u}} (b : K ⟶ f.right) : BiSSet.{u} :=
  pullback f.hom b

def replacementBiFibre (f : Arrow BiSSet.{u}) {K : BiSSet.{u}}
    (b : K ⟶ f.right) : BiSSet.{u} :=
  pullback (relativeReplacement.obj f).hom (b ≫ baseUnit f)

def biComparison (f : Arrow BiSSet.{u}) {K : BiSSet.{u}} (b : K ⟶ f.right) :
    originalBiFibre f b ⟶ replacementBiFibre f b :=
  pullback.lift (pullback.fst f.hom b ≫ totalUnit f) (pullback.snd f.hom b) (by
    rw [Category.assoc, unit_square, pullback.condition_assoc])

theorem biComparison_fst (f : Arrow BiSSet.{u}) {K : BiSSet.{u}} (b : K ⟶ f.right) :
    biComparison f b ≫ pullback.fst (relativeReplacement.obj f).hom (b ≫ baseUnit f) =
      pullback.fst f.hom b ≫ totalUnit f := by
  simp only [biComparison, pullback.lift_fst]

theorem biComparison_snd (f : Arrow BiSSet.{u}) {K : BiSSet.{u}} (b : K ⟶ f.right) :
    biComparison f b ≫ pullback.snd (relativeReplacement.obj f).hom (b ≫ baseUnit f) =
      pullback.snd f.hom b := by
  simp only [biComparison, pullback.lift_snd]

def imageComparison (F : BiSSet.{u} ⥤ SSet.{u}) (f : Arrow BiSSet.{u})
    {K : BiSSet.{u}} (b : K ⟶ f.right) :
    pullback (F.map f.hom) (F.map b) ⟶
      pullback (F.map (relativeReplacement.obj f).hom) (F.map (b ≫ baseUnit f)) :=
  fibreMap (F.map f.hom) (F.map (relativeReplacement.obj f).hom)
    (F.map (totalUnit f)) (F.map (baseUnit f)) (by
      rw [← F.map_comp, ← F.map_comp, unit_square])
    (F.map b) (F.map (b ≫ baseUnit f)) (F.map_comp b (baseUnit f)).symm

theorem imageComparison_square (F : BiSSet.{u} ⥤ SSet.{u}) [PreservesLimits F]
    (f : Arrow BiSSet.{u}) {K : BiSSet.{u}} (b : K ⟶ f.right) :
    F.map (biComparison f b) ≫
        (PreservesPullback.iso F (relativeReplacement.obj f).hom (b ≫ baseUnit f)).hom =
      (PreservesPullback.iso F f.hom b).hom ≫ imageComparison F f b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, PreservesPullback.iso_hom_fst, imageComparison, fibreMap_fst]
    rw [← F.map_comp, biComparison_fst, F.map_comp, ← Category.assoc,
      PreservesPullback.iso_hom_fst]
  · simp only [Category.assoc, PreservesPullback.iso_hom_snd, imageComparison, fibreMap_snd]
    rw [← F.map_comp, biComparison_snd]

end
end DaggerNativeRelativeReedyBisimplicialFibres
