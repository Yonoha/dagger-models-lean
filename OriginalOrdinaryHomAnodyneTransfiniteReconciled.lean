import OriginalOrdinaryHomTransfiniteReconciled
import OrdinaryAnodyneTensor
import IinjBridge

/-!
# Transfinite closure of original ordinary local Hom anodyne maps

The actual ordinary transfinite arrow has anodyne original Hom maps when
all its successor arrows do. The existing local Hom property is reused;
the same conclusion also holds for each original tail arrow.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OriginalOrdinaryHomTransfinite

noncomputable section

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {X Y : SimplicialCat.{u, u}} {f : X ⟶ Y}
variable (h : CategoryTheory.TransfiniteCompositionOfShape J f)
variable (hlocal : ∀ j, ¬IsMax j →
  OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u}
    (h.F.map (homOfLE (Order.le_succ j))))

include h hlocal in
/-- Every actual original Hom map of the same transfinite arrow is anodyne. -/
theorem localAnodyne_of_transfinite :
    OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u} f :=
  fun x y ↦ SSet.anodyneExtensions.transfiniteCompositionsOfShape_le J (f.map x y)
    (homTransfinite h hlocal x y).mem

include h hlocal in
/-- Each actual original Hom map is a monomorphism. -/
theorem hom_mono (x y : X.Obj) : Mono (f.map x y) := by
  letI : Cofibration (f.map x y) := (mem_trivialCofibrations_iff _).1
    ((DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
      (localAnodyne_of_transfinite h hlocal x y)) |>.1
  infer_instance

include h hlocal in
/-- Each actual original Hom map satisfies the exact geometric weak-equivalence predicate. -/
theorem hom_geometric (x y : X.Obj) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.map x y))) :=
  (KanQuillenReuse.weakEquivalence_iff_geometric _).1
    ((mem_trivialCofibrations_iff _).1
      ((DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
        (localAnodyne_of_transfinite h hlocal x y))).2

/-- The existing ordinary local Hom property on the same transfinite record. -/
def localRecord :
    MorphismProperty.TransfiniteCompositionOfShape
      (OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u}) J f where
  __ := h
  map_mem := hlocal

/-- The same original tail has a full anodyne Hom transfinite record. -/
def homTailTransfinite (j0 : J) (x y : (h.F.obj j0).Obj) :
    SSet.anodyneExtensions.TransfiniteCompositionOfShape (Set.Ici j0)
      ((h.incl.app j0).map x y) :=
  homTransfinite (h.ici j0) ((localRecord h hlocal).ici j0).map_mem x y

include hlocal in
/-- Every actual original tail arrow is locally anodyne. -/
theorem tail_localAnodyne (j0 : J) :
    OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u}
      (h.incl.app j0) :=
  localAnodyne_of_transfinite (h.ici j0) ((localRecord h hlocal).ici j0).map_mem

include hlocal in
/-- Every original tail Hom map is a monomorphism. -/
theorem tail_mono (j0 : J) (x y : (h.F.obj j0).Obj) :
    Mono ((h.incl.app j0).map x y) :=
  hom_mono (h.ici j0) ((localRecord h hlocal).ici j0).map_mem x y

include hlocal in
/-- Every original tail Hom map satisfies the exact geometric predicate. -/
theorem tail_geometric (j0 : J) (x y : (h.F.obj j0).Obj) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map ((h.incl.app j0).map x y))) :=
  hom_geometric (h.ici j0) ((localRecord h hlocal).ici j0).map_mem x y

end

/-- The existing ordinary local Hom anodyne class is closed under any shape `J`. -/
instance localAnodyne_transfiniteOfShape (J : Type u)
    [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u}) J where
  le _ _ _ hf := localAnodyne_of_transfinite hf.some.toTransfiniteCompositionOfShape
    hf.some.map_mem

/-- The existing ordinary local Hom anodyne class is transfinite-stable at universe `u`. -/
instance localAnodyne_transfinite :
    MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      (OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u}) where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ := inferInstance

/-- All common-universe transfinite composites lie in the existing local Hom class. -/
theorem transfiniteCompositions_le_localHomAnodyne :
    MorphismProperty.transfiniteCompositions.{u}
      (OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u}) ≤
        OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u} :=
  MorphismProperty.transfiniteCompositions_le _

end DaggerModels.OriginalOrdinaryHomTransfinite
