import NativeReedyRelativeReplacement
import NativeBisimplicialDiagonal
import NativeSSetFibrationSquareFibreWeak

/-! Exact original diagonal fibre comparisons retain the original point object and square maps. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialDiagonal
open DaggerNativeReedyRelativeReplacement DaggerNativeSSetFibrationSquareFibreWeak
universe u
namespace DaggerNativeReedyReplacementFibres
noncomputable section

theorem diagonal_arrow_square {f g : Arrow BiSSet.{u}} (s : f ⟶ g) :
    diagonalFunctor.map f.hom ≫ diagonalFunctor.map s.right =
      diagonalFunctor.map s.left ≫ diagonalFunctor.map g.hom := by
  have hw := s.w
  change s.left ≫ g.hom = f.hom ≫ s.right at hw
  rw [← diagonalFunctor.map_comp, ← diagonalFunctor.map_comp, hw]

theorem diagonal_unit_square (f : Arrow BiSSet.{u}) :
    diagonalFunctor.map (totalUnit f) ≫ diagonalFunctor.map (relativeReplacement.obj f).hom =
      diagonalFunctor.map f.hom ≫ diagonalFunctor.map (baseUnit f) := by
  rw [← diagonalFunctor.map_comp, ← diagonalFunctor.map_comp, unit_square]

def originalFibre (f : Arrow BiSSet.{u}) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) : SSet.{u} := pullback (diagonalFunctor.map f.hom) b

def replacementFibre (f : Arrow BiSSet.{u}) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) : SSet.{u} :=
  pullback (diagonalFunctor.map (relativeReplacement.obj f).hom)
    (b ≫ diagonalFunctor.map (baseUnit f))

def comparison (f : Arrow BiSSet.{u}) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) : originalFibre f b ⟶ replacementFibre f b :=
  fibreMap (diagonalFunctor.map f.hom) (diagonalFunctor.map (relativeReplacement.obj f).hom)
    (diagonalFunctor.map (totalUnit f)) (diagonalFunctor.map (baseUnit f))
    (diagonal_unit_square f).symm b (b ≫ diagonalFunctor.map (baseUnit f)) rfl

theorem comparison_fst (f : Arrow BiSSet.{u}) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) : comparison f b ≫
      pullback.fst (diagonalFunctor.map (relativeReplacement.obj f).hom)
        (b ≫ diagonalFunctor.map (baseUnit f)) =
      pullback.fst (diagonalFunctor.map f.hom) b ≫ diagonalFunctor.map (totalUnit f) :=
  fibreMap_fst _ _ _ _ _ _ _ _

theorem comparison_snd (f : Arrow BiSSet.{u}) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) : comparison f b ≫
      pullback.snd (diagonalFunctor.map (relativeReplacement.obj f).hom)
        (b ≫ diagonalFunctor.map (baseUnit f)) = pullback.snd (diagonalFunctor.map f.hom) b :=
  fibreMap_snd _ _ _ _ _ _ _ _

def originalFibreMap {f g : Arrow BiSSet.{u}} (s : f ⟶ g) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) (c : T ⟶ diagonalFunctor.obj g.right)
    (hb : b ≫ diagonalFunctor.map s.right = c) : originalFibre f b ⟶ originalFibre g c :=
  fibreMap _ _ (diagonalFunctor.map s.left) (diagonalFunctor.map s.right)
    (diagonal_arrow_square s) b c hb

theorem replacedPoint_natural {f g : Arrow BiSSet.{u}} (s : f ⟶ g) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) (c : T ⟶ diagonalFunctor.obj g.right)
    (hb : b ≫ diagonalFunctor.map s.right = c) :
    (b ≫ diagonalFunctor.map (baseUnit f)) ≫ diagonalFunctor.map
        (relativeReplacement.map s).right = c ≫ diagonalFunctor.map (baseUnit g) := by
  rw [Category.assoc, ← diagonalFunctor.map_comp, baseUnit_natural,
    diagonalFunctor.map_comp, ← Category.assoc, hb]

def replacementFibreMap {f g : Arrow BiSSet.{u}} (s : f ⟶ g) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) (c : T ⟶ diagonalFunctor.obj g.right)
    (hb : b ≫ diagonalFunctor.map s.right = c) : replacementFibre f b ⟶ replacementFibre g c :=
  fibreMap _ _ (diagonalFunctor.map (relativeReplacement.map s).left)
    (diagonalFunctor.map (relativeReplacement.map s).right)
    (diagonal_arrow_square (relativeReplacement.map s))
    (b ≫ diagonalFunctor.map (baseUnit f)) (c ≫ diagonalFunctor.map (baseUnit g))
    (replacedPoint_natural s b c hb)

theorem comparison_natural {f g : Arrow BiSSet.{u}} (s : f ⟶ g) {T : SSet.{u}}
    (b : T ⟶ diagonalFunctor.obj f.right) (c : T ⟶ diagonalFunctor.obj g.right)
    (hb : b ≫ diagonalFunctor.map s.right = c) :
    comparison f b ≫ replacementFibreMap s b c hb = originalFibreMap s b c hb ≫
      comparison g c := by
  apply pullback.hom_ext
  · simp only [replacementFibreMap, originalFibreMap, Category.assoc, fibreMap_fst,
      comparison_fst]
    rw [← Category.assoc, comparison_fst, Category.assoc, ← diagonalFunctor.map_comp,
      totalUnit_natural, diagonalFunctor.map_comp]
    simp only [← Category.assoc]
    rw [fibreMap_fst]
  · simp only [replacementFibreMap, originalFibreMap, Category.assoc, fibreMap_snd,
      comparison_snd]

end
end DaggerNativeReedyReplacementFibres
