import OriginalOrdinaryHornGenerators
import OriginalOrdinaryObjectCells
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Object functions in the ordinary horn-cell left class

The actual original horn-cell generators act bijectively on objects. The
small-object retract description and the accepted ordinary cell closure
extend this fact to their entire left lifting class. No statement about
mapping-space weak equivalences is made.
-/

open CategoryTheory MorphismProperty

universe u

namespace DaggerModels.OriginalOrdinaryHornObjectBijections

open OriginalOrdinaryHornGenerators DaggerOriginalOrdinaryObjectCells

/-- Every literal ordinary horn-cell generator is bijective on objects. -/
theorem generators_le_objectBijections :
    generators.{u} ≤ objectBijections.{u} := by
  intro _ _ i hi
  change MorphismProperty.ofHoms generator i at hi
  cases hi with
  | mk a =>
    exact ordinaryMap_objectBijections (SSet.horn (a.1 + 1) a.2).ι

private theorem hornCellClosure_le_objectBijections :
    MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.pushouts
        (MorphismProperty.coproducts.{u} generators.{u})) ≤
      objectBijections.{u} := by
  intro _ _ i hi
  apply (objectBijections_iff i).2
  apply cellClosure_object_bijective i
  exact (transfiniteCompositions_monotone
    (pushouts_monotone
      (coproducts_monotone generators_le_objectBijections))) i hi

/-- The whole left lifting class of the ordinary horn family has bijective
object functions, including the retracts in the small-object description. -/
theorem generators_rlp_llp_le_objectBijections :
    generators.{u}.rlp.llp ≤ objectBijections.{u} := by
  letI : MorphismProperty.HasSmallObjectArgument.{u} generators.{u} :=
    generators_hasSmallObjectArgument
  letI : objectBijections.{u}.IsStableUnderRetracts := by
    change ((isomorphisms (Type u)).inverseImage SimplicialCat.objects).IsStableUnderRetracts
    infer_instance
  rw [MorphismProperty.llp_rlp_of_hasSmallObjectArgument]
  exact (MorphismProperty.retracts_le_iff).2 hornCellClosure_le_objectBijections

/-- A map in the literal horn-cell left class is a bijection on original
objects. -/
theorem object_bijective_of_generators_rlp_llp {C D : SimplicialCat.{u, u}}
    (i : C ⟶ D) (hi : generators.rlp.llp i) : Function.Bijective i.obj :=
  (objectBijections_iff i).mp (generators_rlp_llp_le_objectBijections i hi)

end DaggerModels.OriginalOrdinaryHornObjectBijections
