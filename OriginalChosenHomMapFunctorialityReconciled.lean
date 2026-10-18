import ChosenFlagOriginalHomNaturality

/-!
# Literal functoriality of the original chosen Hom map

The original map retains both `RV` endpoint transports. These identities
follow from the already proved natural flag/original Hom isomorphism and
the actual postcomposition laws of chosen flags.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalChosenHomMapFunctoriality

noncomputable section

variable {X Y Z : SSet.{u}} (a b : X.obj (op ⦋0⦌))

/-- The map of the original identity preserves the entire chosen Hom. -/
theorem originalChosenHomMap_id :
    originalChosenHomMap (𝟙 X) a b =
      𝟙 (RV X a ⟶[SSet.{u}] RV X b) := by
  apply (cancel_epi (flagOriginalHomIso X a b).hom).mp
  rw [← flagOriginalHomIso_naturality (f := (𝟙 X)) a b]
  rw [flagHomMap_id, Category.id_comp, Category.comp_id]
  simp only [SSet.id_app, types_id_apply]

/-- The original Hom map takes composition to composition as whole maps. -/
theorem originalChosenHomMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    originalChosenHomMap (f ≫ g) a b =
      originalChosenHomMap f a b ≫
        originalChosenHomMap g (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) := by
  apply (cancel_epi (flagOriginalHomIso X a b).hom).mp
  rw [← flagOriginalHomIso_naturality (f := (f ≫ g)) a b]
  rw [flagHomMap_comp, Category.assoc]
  simp only [SSet.comp_app, types_comp_apply]
  rw [flagOriginalHomIso_naturality g
    (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)]
  rw [← Category.assoc, flagOriginalHomIso_naturality f a b]
  simp only [Category.assoc]

end

end DaggerOriginalChosenHomMapFunctoriality
