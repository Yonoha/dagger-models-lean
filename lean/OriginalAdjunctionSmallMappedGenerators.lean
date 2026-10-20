import OriginalAdjunctionMappedLifting
import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# Small actual image families for adjoint lifting transfer

Use the literal images of the original generating family. An isomorphism closure need not
be a small set of arrows; the literal image family is small and has exactly the same right
lifting class. This changes no intended right or left model class.
-/
set_option autoImplicit false
open CategoryTheory
universe u v a b w
namespace DaggerOriginalAdjunctionSmallMappedGenerators
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]

/-- Keep the literal image of each original generator, before taking any isomorphism closure. -/
def mappedFamilyClass (I : MorphismProperty C) (L : C ⥤ D) : MorphismProperty D :=
  MorphismProperty.ofHoms (fun i : I.toSet ↦ L.map i.1.hom)

/-- A literal image of a small family is a small family in the same universe. -/
instance mappedFamilyClass_isSmall (I : MorphismProperty C)
    [MorphismProperty.IsSmall.{w} I] (L : C ⥤ D) :
    MorphismProperty.IsSmall.{w} (mappedFamilyClass I L) := by
  unfold mappedFamilyClass
  infer_instance

/-- Every original generator is retained, with the exact same adjoint right lifting condition. -/
theorem mappedFamilyClass_rlp_eq {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (I : MorphismProperty C) : (mappedFamilyClass I L).rlp = I.rlp.inverseImage R := by
  funext X Y p
  apply propext
  constructor
  · intro h A B i hi
    apply (adj.hasLiftingProperty_iff i p).mp
    apply h (L.map i)
    change MorphismProperty.ofHoms (fun j : I.toSet ↦ L.map j.1.hom) (L.map i)
    exact ⟨(⟨Arrow.mk i, hi⟩ : I.toSet)⟩
  · intro h A B i hi
    rcases hi with ⟨j⟩
    exact (adj.hasLiftingProperty_iff j.1.hom p).mpr (h j.1.hom j.2)

end DaggerOriginalAdjunctionSmallMappedGenerators
