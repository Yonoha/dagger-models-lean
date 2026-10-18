import OrdinaryCellAcyclicity
import SimplicialIsoHoms
import DaggerModels.TwoObjectCellReductionResolved
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-! Transfer the existing ordinary-cell result to the same original dagger pushout.
Both ordinary copies, all three comparison legs and the original Hom maps are retained. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
open TwoObjectCellReduction

universe u

namespace DaggerCellHomTransfer

noncomputable section

section Ordinary

variable {K L : SSet.{u}} {C D : SimplicialCat.{u, u}} (i : K ⟶ L)
  (d : OrdinaryTwoObjectCell.cell K ⟶ C) (g : OrdinaryTwoObjectCell.cell L ⟶ D)
  (f : C ⟶ D) (sq : IsPushout (OrdinaryTwoObjectCell.map i) d g f) [Mono i]

include sq

/-- Classify the given attaching functor, without replacing its endpoints or original square. -/
theorem ordinary_hom_mono : ∀ x y : C.Obj, Mono (f.map x y) := by
  exact (DaggerOrdinaryCellAcyclicity.ordinary_cell C
    (d.obj TwoObjectDaggerGraph.left) (d.obj TwoObjectDaggerGraph.right) i
    (d.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right) g f
    (by simpa only [OrdinaryTwoObjectCell.fromData_classify] using sq)).2.1

theorem ordinary_hom_anodyne
    (hi : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i))) :
    ∀ x y : C.Obj, SSet.anodyneExtensions (f.map x y) := by
  intro x y
  exact DaggerOrdinaryCellAcyclicity.original_hom_anodyne C
    (d.obj TwoObjectDaggerGraph.left) (d.obj TwoObjectDaggerGraph.right) x y i
    (d.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right) g f
    (by simpa only [OrdinaryTwoObjectCell.fromData_classify] using sq) hi

end Ordinary

attribute [local instance] DaggerModels.simplicialCatHasColimits

variable {K L : SSet.{u}} {C P : DaggerSimplicialCat.{u, u}}
  (i : K ⟶ L) (a : TwoObjectDaggerCell.cell K ⟶ C)
  {b : TwoObjectDaggerCell.cell L ⟶ P} {c : C ⟶ P}
  (sq : IsPushout (TwoObjectDaggerCell.functor.map i) a b c)

include sq

/-- Compare the given dagger pushout with the existing two successive ordinary pushouts. -/
def comparison : P.toSimplicialCat ≅ successiveAttachment i a :=
  comparisonIso a i (firstAttachment_isPushout i a) (secondAttachment_isPushout i a) sq

theorem comparison_original :
    DaggerSimplicialCat.forget.map c ≫ (comparison i a sq).hom =
      firstOriginalInclusion i a ≫ secondOriginalInclusion i a :=
  comparisonIso_original a i _ _ sq

theorem comparison_forward :
    (TwoObjectCellPushout.inl L ≫ DaggerSimplicialCat.forget.map b) ≫
      (comparison i a sq).hom = firstCellInclusion i a ≫ secondOriginalInclusion i a :=
  comparisonIso_forward a i _ _ sq

theorem comparison_reverse :
    (TwoObjectCellPushout.inr L ≫ DaggerSimplicialCat.forget.map b) ≫
      (comparison i a sq).hom = secondCellInclusion i a :=
  comparisonIso_reverse a i _ _ sq

/-- Compose properties on the two actual ordinary inclusions and return to the original c. -/
theorem hom_property (Q : MorphismProperty SSet.{u})
    [Q.RespectsIso] [Q.IsStableUnderComposition]
    (h₀ : ∀ x y : C.Obj, Q ((firstOriginalInclusion i a).map x y))
    (h₁ : ∀ x y : (firstAttachment i a).Obj,
      Q ((secondOriginalInclusion i a).map x y)) :
    ∀ x y : C.Obj, Q (c.map x y) := by
  have hh : ∀ x y : C.Obj,
      Q ((DaggerSimplicialCat.forget.map c ≫ (comparison i a sq).hom).map x y) := by
    rw [comparison_original]
    intro x y
    exact Q.comp_mem _ _ (h₀ x y)
      (h₁ ((firstOriginalInclusion i a).obj x) ((firstOriginalInclusion i a).obj y))
  intro x y
  exact (Q.arrow_mk_iso_iff (DaggerSimplicialIsoHoms.postcompArrowIso
    (comparison i a sq) (c.obj x) (c.obj y) (c.map x y))).2 (hh x y)

variable [Mono i]

/-- Every Hom map of the original dagger-cell inclusion is monic. -/
theorem dagger_cell_hom_mono : ∀ x y : C.Obj, Mono (c.map x y) := by
  exact hom_property i a sq (MorphismProperty.monomorphisms SSet.{u})
    (ordinary_hom_mono i (forwardAttaching a) _ _ (firstAttachment_isPushout i a))
    (ordinary_hom_mono i (reverseAttaching a ≫ firstOriginalInclusion i a) _ _
      (secondAttachment_isPushout i a))

variable (hi : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i)))

include hi

/-- A mono geometric weak equivalence attaches anodyne maps on all original Hom spaces. -/
theorem dagger_cell_hom_anodyne : ∀ x y : C.Obj, SSet.anodyneExtensions (c.map x y) := by
  exact hom_property i a sq SSet.anodyneExtensions
    (ordinary_hom_anodyne i (forwardAttaching a) _ _ (firstAttachment_isPushout i a) hi)
    (ordinary_hom_anodyne i (reverseAttaching a ≫ firstOriginalInclusion i a) _ _
      (secondAttachment_isPushout i a) hi)

theorem dagger_cell_hom_trivialCofibration :
    ∀ x y : C.Obj, trivialCofibrations SSet.{u} (c.map x y) := by
  intro x y
  exact (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
    (dagger_cell_hom_anodyne i a sq hi x y)

/-- The conclusion uses the same original geometric predicate on the same original Hom map. -/
theorem dagger_cell_hom_geometric : ∀ x y : C.Obj,
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (c.map x y))) := by
  intro x y
  exact (KanQuillenReuse.weakEquivalence_iff_geometric (c.map x y)).1
    ((mem_trivialCofibrations_iff (c.map x y)).1
      (dagger_cell_hom_trivialCofibration i a sq hi x y)).2

end

end DaggerCellHomTransfer
