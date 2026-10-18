import OriginalOrdinaryHornPushoutAnodyne
import OriginalOrdinaryHomAnodyneTransfiniteReconciled
import DaggerModels.SimplicialColimits
import CoproductCellSerialization
import OrdinaryAnodyneTensor
import IinjBridge
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Anodyne original Hom maps in the literal ordinary horn left class

The actual ordinary horn-cell pushouts have anodyne original Hom maps.
Generic coproduct serialization, transfinite closure and the small object
argument extend this to the literal horn left lifting class, with no
restriction on objects or original Hom simplicial sets.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OriginalOrdinaryHornLeftClassAnodyne

open OriginalOrdinaryHornGenerators

noncomputable section

/-- Actual pushouts of literal ordinary horn cells have anodyne source Hom maps. -/
theorem generators_pushouts_le_localAnodyne :
    generators.{u}.pushouts ≤
      OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u} := by
  intro C D f hf
  exact OriginalOrdinaryHornPushoutAnodyne.generators_pushouts_hom_anodyne f hf

/-- Serializing any coproduct pushout retains its original arrow and local Hom property. -/
theorem generators_coproduct_pushouts_le_localAnodyne :
    (MorphismProperty.coproducts.{u} generators.{u}).pushouts ≤
      OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u} := by
  letI : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
    SimplicialCat.SemanticColimit.simplicialCatHasColimits
  letI : HasCoproducts.{u} SimplicialCat.{u, u} := inferInstance
  letI : HasPushouts SimplicialCat.{u, u} := inferInstance
  exact (DaggerCoproductCellSerialization.coproduct_pushouts_le generators.{u}).trans
    ((MorphismProperty.transfiniteCompositions_monotone
      generators_pushouts_le_localAnodyne).trans
        OriginalOrdinaryHomTransfinite.transfiniteCompositions_le_localHomAnodyne)

/-- Every actual common-universe transfinite horn-cell complex is locally anodyne. -/
theorem generators_cellComplex_le_localAnodyne :
    MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} generators.{u}).pushouts ≤
        OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u} :=
  (MorphismProperty.transfiniteCompositions_le_iff).2
    generators_coproduct_pushouts_le_localAnodyne

/-- The literal ordinary horn left class has anodyne maps on all original Homs. -/
theorem hornLeft_le_localAnodyne :
    generators.{u}.rlp.llp ≤
      OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u} := by
  letI : MorphismProperty.HasSmallObjectArgument.{u} generators.{u} :=
    generators_hasSmallObjectArgument
  rw [MorphismProperty.llp_rlp_of_hasSmallObjectArgument]
  exact (MorphismProperty.retracts_le_iff).2 generators_cellComplex_le_localAnodyne

/-- Every original Hom of an actual horn-left arrow is anodyne. -/
theorem hornLeft_hom_anodyne {C D : SimplicialCat.{u, u}} (f : C ⟶ D)
    (hf : generators.rlp.llp f) (x y : C.Obj) :
    SSet.anodyneExtensions (f.map x y) :=
  hornLeft_le_localAnodyne f hf x y

/-- Every original Hom of an actual horn-left arrow is monic. -/
theorem hornLeft_hom_mono {C D : SimplicialCat.{u, u}} (f : C ⟶ D)
    (hf : generators.rlp.llp f) (x y : C.Obj) : Mono (f.map x y) := by
  letI : Cofibration (f.map x y) := (mem_trivialCofibrations_iff _).1
    ((DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
      (hornLeft_hom_anodyne f hf x y)) |>.1
  infer_instance

/-- Every original Hom of an actual horn-left arrow satisfies the exact geometric predicate. -/
theorem hornLeft_hom_geometric {C D : SimplicialCat.{u, u}} (f : C ⟶ D)
    (hf : generators.rlp.llp f) (x y : C.Obj) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.map x y))) :=
  (KanQuillenReuse.weakEquivalence_iff_geometric _).1
    ((mem_trivialCofibrations_iff _).1
      ((DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
        (hornLeft_hom_anodyne f hf x y))).2

end

end DaggerModels.OriginalOrdinaryHornLeftClassAnodyne
