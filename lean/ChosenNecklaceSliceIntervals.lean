import ChosenNecklaceSlicePushout
import ChosenNecklaceIntervalPaths

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool)

def sideStart : Fin (T.len + 1) := if right then j else 0

def sideEnd : Fin (T.len + 1) := if right then Fin.last T.len else j

theorem sideLe : sideStart T j right ≤ sideEnd T j right := by
  cases right
  · exact Fin.zero_le j
  · exact Fin.le_last j

abbrev sideCode : NecklaceCode := intervalCode T (sideStart T j right) (sideEnd T j right)
  (sideLe T j right)

theorem sideBounds (a : SliceObjects.{u} T j right) :
    sideStart T j right ≤ a.val.down ∧ a.val.down ≤ sideEnd T j right := by
  cases right
  · exact ⟨Fin.zero_le _, a.property⟩
  · exact ⟨a.property, Fin.le_last _⟩

theorem sideMem (a : Fin (T.len + 1))
    (ha : sideStart T j right ≤ a) (hb : a ≤ sideEnd T j right) :
    if right then (ULift.up j : Vertices.{u} T) ≤ ULift.up a
      else (ULift.up a : Vertices.{u} T) ≤ ULift.up j := by
  cases right
  · exact hb
  · exact ha

def sideVertexMap (a : Vertices.{u} (sideCode T j right)) : SliceObjects.{u} T j right :=
  ⟨intervalOrderMap T (sideStart T j right) (sideEnd T j right) (sideLe T j right) a,
    sideMem T j right _
      (intervalEmbedding_bounds T (sideStart T j right) (sideEnd T j right)
        (sideLe T j right) a.down).1
      (intervalEmbedding_bounds T (sideStart T j right) (sideEnd T j right)
        (sideLe T j right) a.down).2⟩

def sideVertexUnmap (a : SliceObjects.{u} T j right) : Vertices.{u} (sideCode T j right) :=
  ULift.up ⟨a.val.down.val - (sideStart T j right).val, by
    have ha := (sideBounds T j right a).1
    have hb := (sideBounds T j right a).2
    change (sideStart T j right).val ≤ a.val.down.val at ha
    change a.val.down.val ≤ (sideEnd T j right).val at hb
    change a.val.down.val - (sideStart T j right).val <
      (sideEnd T j right).val - (sideStart T j right).val + 1
    omega⟩

theorem sideVertexMap_unmap (a : SliceObjects.{u} T j right) :
    sideVertexMap T j right (sideVertexUnmap T j right a) = a := by
  apply Subtype.ext
  apply ULift.ext
  apply Fin.ext
  have ha := (sideBounds T j right a).1
  change (sideStart T j right).val ≤ a.val.down.val at ha
  change (sideStart T j right).val +
    (a.val.down.val - (sideStart T j right).val) = a.val.down.val
  omega

theorem sideVertexUnmap_map (a : Vertices.{u} (sideCode T j right)) :
    sideVertexUnmap T j right (sideVertexMap T j right a) = a := by
  apply ULift.ext
  apply Fin.ext
  change ((sideStart T j right).val + a.down.val) - (sideStart T j right).val = a.down.val
  omega

/-- Both object inverse laws on the same original lifted vertices, including point intervals. -/
def sideObjectEquiv : (NC.{u} (sideCode T j right)).Obj ≃ (slice.{u} T j right).Obj where
  toFun a := sideVertexMap T j right a.as
  invFun a := ⟨sideVertexUnmap T j right a⟩
  left_inv a := congrArg NecklaceThickening.mk (sideVertexUnmap_map T j right a.as)
  right_inv := sideVertexMap_unmap T j right

/-- Original interval inclusion into the actual full enriched slice. -/
def sideNCMap : NC.{u} (sideCode T j right) ⟶ slice.{u} T j right where
  obj := sideObjectEquiv T j right
  map a b := (intervalHomIso T (sideStart T j right) (sideEnd T j right)
    (sideLe T j right) a.as b.as).hom
  map_id a := by
    ext q v
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext Set.image_singleton)
  map_comp a b c := by
    ext q v
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext (Set.image_union _ _ _))

/-- Full all-degree Hom inverse, for arbitrary pairs of original slice vertices. -/
def sideHomIso (a b : (NC.{u} (sideCode T j right)).Obj) :
    (a ⟶[SSet.{u}] b) ≅ ((sideNCMap T j right).obj a ⟶[SSet.{u}]
      (sideNCMap T j right).obj b) :=
  intervalHomIso T (sideStart T j right) (sideEnd T j right) (sideLe T j right) a.as b.as

theorem sideHomIso_hom (a b : (NC.{u} (sideCode T j right)).Obj) :
    (sideHomIso T j right a b).hom = (sideNCMap T j right).map a b := rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
