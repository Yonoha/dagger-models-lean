import ChosenNecklaceSliceIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

open CategoryTheory Limits EnrichedCategory MonoidalCategory

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable (T : NecklaceCode) (j : Fin (T.len + 1))

def cutPointLeg (right : Bool) : NC.{u} point ⟶ NC.{u} (sideCode T j right) :=
  pointNCFunctor _ ⟨ULift.up (if right then 0 else Fin.last (sideCode T j right).len)⟩

def cutNCInclusion (right : Bool) : NC.{u} (sideCode T j right) ⟶ NC.{u} T :=
  (sideIso T j right).hom ≫ sliceInclusion T j right

theorem cutPointLeg_sideIso (right : Bool) :
    cutPointLeg.{u} T j right ≫ (sideIso T j right).hom = slicePointLeg T j right := by
  apply pointNCFunctor_ext
  apply Subtype.ext
  apply ULift.ext
  cases right
  · change intervalEmbedding T 0 j (Fin.zero_le j) (Fin.last (j.val - 0)) = j
    exact intervalEmbedding_last T 0 j (Fin.zero_le j)
  · change intervalEmbedding T j (Fin.last T.len) (Fin.le_last j) 0 = j
    exact intervalEmbedding_first T j (Fin.last T.len) (Fin.le_last j)

theorem cutNC_comm :
    cutPointLeg.{u} T j false ≫ cutNCInclusion T j false =
      cutPointLeg T j true ≫ cutNCInclusion T j true := by
  simp only [cutNCInclusion, ← Category.assoc, cutPointLeg_sideIso]
  exact slicePoint_comm T j

/-- The same full arbitrary-target joint UP with actual interval objects and all Hom inverses. -/
theorem cutNCIsPushout (hj : j ∈ T.joints) :
    IsPushout (cutPointLeg.{u} T j false) (cutPointLeg T j true)
      (cutNCInclusion T j false) (cutNCInclusion T j true) := by
  apply (sliceIsPushout T j hj).of_iso'
    (Iso.refl _) (sideIso T j false) (sideIso T j true) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.id_comp] using (cutPointLeg_sideIso T j false).symm
  · simpa only [Iso.refl_hom, Category.id_comp] using (cutPointLeg_sideIso T j true).symm
  · simp only [cutNCInclusion, Iso.refl_hom, Category.comp_id]
  · simp only [cutNCInclusion, Iso.refl_hom, Category.comp_id]

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
