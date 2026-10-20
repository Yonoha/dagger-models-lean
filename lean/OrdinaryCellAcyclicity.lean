import OrdinaryWordFiltration
import OrdinaryWordStages
import OrdinaryCellComparison
import OrdinaryCellMonicity
import IinjBridge

/-! The original ordinary-cell lemma on every original enriched pushout and Hom map.
The acyclic assertion uses the original geometric weak-equivalence predicate. -/

open CategoryTheory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
open DaggerRelativeOneCellPresentation DaggerOrdinaryWordFiltration
open DaggerOrdinaryWordStages DaggerOrdinaryCellImage DaggerOrdinaryCellComparison

universe u

namespace DaggerOrdinaryCellAcyclicity

noncomputable section

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) {L : SSet.{u}}
variable (A : L.Subcomplex) (uA : (A : SSet.{u}) ⟶ (x ⟶[SSet] y)) (a b : C.Obj)

/-- Inherit all original transfinite data and add only the actual successor memberships. -/
def anodyneTransfiniteComposition (hA : SSet.anodyneExtensions A.ι) :
    SSet.anodyneExtensions.TransfiniteCompositionOfShape ℕ ((v C x y A.ι uA).map a b) where
  toTransfiniteCompositionOfShape := transfiniteComposition C x y A uA a b
  map_mem n _ := by
    change SSet.anodyneExtensions ((filtration C x y A uA a b).map
      (homOfLE (Order.le_succ n)))
    rw [order_successor_map]
    exact step_anodyne C x y A uA hA n a b

/-- The exact old Hom map into the original quotient is anodyne. -/
theorem presentation_hom_anodyne (hA : SSet.anodyneExtensions A.ι) :
    SSet.anodyneExtensions ((v C x y A.ι uA).map a b) :=
  MorphismProperty.transfiniteCompositionsOfShape_le SSet.anodyneExtensions ℕ _
    ((anodyneTransfiniteComposition C x y A uA a b hA).mem _)

/-- Convert the original geometric predicate without any Kan hypotheses. -/
theorem mono_geometric_anodyne {K L : SSet.{u}} (i : K ⟶ L) [Mono i]
    (hi : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i))) :
    SSet.anodyneExtensions i := by
  letI : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
  letI : WeakEquivalence i := (KanQuillenReuse.weakEquivalence_iff_geometric i).2 hi
  exact (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration i).2
    (mem_trivialCofibrations i)

variable {K : SSet.{u}} (i : K ⟶ L) (u0 : K ⟶ (x ⟶[SSet] y))
  {D : SimplicialCat.{u, u}} (g : OrdinaryTwoObjectCell.cell L ⟶ D) (f : C ⟶ D)
  (sq : IsPushout (OrdinaryTwoObjectCell.map i)
    (OrdinaryTwoObjectCell.fromData K C x y u0) g f) [Mono i]

include g sq

/-- The full image/Arrow comparison returns the SAME original f.map, with its endpoints. -/
theorem original_hom_anodyne
    (hi : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i))) :
    SSet.anodyneExtensions (f.map a b) := by
  have hA : SSet.anodyneExtensions (image i).ι :=
    (property_iff i SSet.anodyneExtensions).1 (mono_geometric_anodyne i hi)
  exact (image_hom_property_iff C x y i u0 g f sq a b SSet.anodyneExtensions).1
    (presentation_hom_anodyne C x y (image i) (attachingMap i u0) a b hA)

theorem original_hom_trivialCofibration
    (hi : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i))) :
    trivialCofibrations SSet.{u} (f.map a b) :=
  (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
    (original_hom_anodyne C x y a b i u0 g f sq hi)

/-- The manuscript's second assertion uses the original geometric predicate explicitly. -/
theorem ordinary_cell_part_two
    (hi : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i))) :
    ∀ a b : C.Obj,
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.map a b))) := by
  intro a b
  exact (KanQuillenReuse.weakEquivalence_iff_geometric (f.map a b)).1
    ((mem_trivialCofibrations_iff (f.map a b)).1
      (original_hom_trivialCofibration C x y a b i u0 g f sq hi)).2

/-- Full bg.lem.ordinary-cell, for any original square and arbitrary original endpoints. -/
theorem ordinary_cell :
    Function.Bijective f.obj ∧ (∀ a b : C.Obj, Mono (f.map a b)) ∧
      (SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i)) → ∀ a b : C.Obj,
        SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.map a b)))) :=
  ⟨(DaggerOrdinaryCellMonicity.ordinary_cell_part_one C x y i u0 g f sq).1,
    (DaggerOrdinaryCellMonicity.ordinary_cell_part_one C x y i u0 g f sq).2,
    ordinary_cell_part_two C x y i u0 g f sq⟩

end

end DaggerOrdinaryCellAcyclicity
