import ChosenNecklaceSlices
import ChosenNecklacePointFunctor

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T : NecklaceCode} (j : Fin (T.len + 1))
variable {D : DaggerModels.SimplicialCat.{u,u}}
variable (F : slice.{u} T j false ⟶ D) (G : slice.{u} T j true ⟶ D)

/-- Arbitrary cocone object labels, using the actual left label at the glued vertex. -/
def sliceLabel (a : Vertices.{u} T) : D.Obj :=
  if ha : a ≤ ULift.up j then F.obj ⟨a, ha⟩
  else G.obj ⟨a, (lt_of_not_ge ha).le⟩

theorem sliceLabel_left (a : (slice.{u} T j false).Obj) :
    sliceLabel j F G a.val = F.obj a := by
  have ha : a.val ≤ ULift.up j := a.property
  rw [sliceLabel, dif_pos ha]
  rfl

variable (h : F.obj (sliceJoint T j false) = G.obj (sliceJoint T j true))

include h in
theorem sliceLabel_right (a : (slice.{u} T j true).Obj) :
    sliceLabel j F G a.val = G.obj a := by
  by_cases ha : a.val ≤ ULift.up j
  · have he : a = sliceJoint T j true := Subtype.ext (le_antisymm ha a.property)
    subst a
    change sliceLabel j F G (ULift.up j) = G.obj (sliceJoint T j true)
    rw [sliceLabel, dif_pos (show (ULift.up j : Vertices.{u} T) ≤ ULift.up j from le_rfl)]
    exact h
  · rw [sliceLabel, dif_neg ha]
    rfl

def leftAligned : slice.{u} T j false ⟶ D :=
  transportObjects F (fun a ↦ sliceLabel j F G a.val)
    (fun a ↦ (sliceLabel_left j F G a).symm)

def rightAligned : slice.{u} T j true ⟶ D :=
  transportObjects G (fun a ↦ sliceLabel j F G a.val)
    (fun a ↦ (sliceLabel_right j F G h a).symm)

/-- Actual supplied functors supply the complete slice data; no global UP is assumed. -/
def sliceCoconeMaps : SliceSSetMaps j D (sliceLabel j F G) where
  left a b ha hb := (leftAligned j F G).map ⟨a, ha⟩ ⟨b, hb⟩
  right a b ha hb := (rightAligned j F G h).map ⟨a, ha⟩ ⟨b, hb⟩
  left_id a ha := (leftAligned j F G).map_id ⟨a, ha⟩
  right_id a ha := (rightAligned j F G h).map_id ⟨a, ha⟩
  left_comp a b c ha hb hc := (leftAligned j F G).map_comp ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
  right_comp a b c ha hb hc := (rightAligned j F G h).map_comp ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
