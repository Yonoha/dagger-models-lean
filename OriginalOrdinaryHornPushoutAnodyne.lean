import OriginalOrdinaryHornGenerators
import OrdinaryCellAcyclicity
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Hom maps of original ordinary horn-cell pushouts

A literal positive-dimensional horn inclusion satisfies the geometric
condition used by the existing original ordinary one-cell theorem. Every
actual pushout of its two-object cell map has anodyne maps on all original
source Hom simplicial sets, for an arbitrary enriched attaching functor.
This makes no transfinite or retract-closure assertion.
-/

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OriginalOrdinaryHornPushoutAnodyne

open OriginalOrdinaryHornGenerators

/-- The literal positive-dimensional horn inclusion is monic. -/
theorem horn_mono (a : Index) : Mono (SSet.horn.{u} (a.1 + 1) a.2).ι := by
  infer_instance

/-- The literal horn inclusion has the geometric weak-equivalence property
required by the existing original ordinary one-cell theorem. -/
theorem horn_geometric (a : Index) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (SSet.horn.{u} (a.1 + 1) a.2).ι)) := by
  have htriv : trivialCofibrations SSet.{u} (SSet.horn.{u} (a.1 + 1) a.2).ι :=
    (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
      (SSet.anodyneExtensions.horn_ι_mem a.1 a.2)
  exact (KanQuillenReuse.weakEquivalence_iff_geometric _).1
    ((mem_trivialCofibrations_iff _).1 htriv).2

/-- Every original Hom map in one actual pushout of a literal horn cell is
anodyne, with arbitrary images of the two source objects. -/
theorem hornPushout_hom_anodyne (a : Index) {C D : SimplicialCat.{u, u}}
    (h : OrdinaryTwoObjectCell.cell (SSet.horn.{u} (a.1 + 1) a.2) ⟶ C)
    (g : OrdinaryTwoObjectCell.cell
      (SSet.stdSimplex.obj (SimplexCategory.mk (a.1 + 1))) ⟶ D)
    (f : C ⟶ D) (sq : IsPushout (generator a) h g f) (x y : C.Obj) :
    SSet.anodyneExtensions (f.map x y) := by
  letI : Mono (SSet.horn.{u} (a.1 + 1) a.2).ι := horn_mono a
  have hs : IsPushout
      (OrdinaryTwoObjectCell.map (SSet.horn.{u} (a.1 + 1) a.2).ι)
      (OrdinaryTwoObjectCell.fromData _ C
        (h.obj TwoObjectDaggerGraph.left) (h.obj TwoObjectDaggerGraph.right)
        (h.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right)) g f := by
    change IsPushout (OrdinaryTwoObjectCell.map _) h g f at sq
    rw [← OrdinaryTwoObjectCell.fromData_classify h] at sq
    exact sq
  exact DaggerOrdinaryCellAcyclicity.original_hom_anodyne C
    (h.obj TwoObjectDaggerGraph.left) (h.obj TwoObjectDaggerGraph.right)
    x y (SSet.horn.{u} (a.1 + 1) a.2).ι
    (h.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right)
    g f hs (horn_geometric a)

/-- Every actual pushout in the literal original horn-cell family has
anodyne maps on all Hom simplicial sets of its original source. -/
theorem generators_pushouts_hom_anodyne {C D : SimplicialCat.{u, u}}
    (f : C ⟶ D) (hf : generators.pushouts f) :
    ∀ x y : C.Obj, SSet.anodyneExtensions (f.map x y) := by
  rcases hf with ⟨A, B, i, h, g, hi, sq⟩
  change MorphismProperty.ofHoms generator i at hi
  cases hi with
  | mk a =>
    intro x y
    exact hornPushout_hom_anodyne a h g f sq.flip x y

end DaggerModels.OriginalOrdinaryHornPushoutAnodyne
