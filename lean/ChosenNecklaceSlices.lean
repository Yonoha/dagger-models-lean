import ChosenNecklaceEnrichment

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

/-- Original vertices on one side of the actual joint; Homs remain the original full Homs. -/
def SliceObjects (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool) : Type u :=
  {a : Vertices.{u} T // if right then ULift.up j ≤ a else a ≤ ULift.up j}

instance sliceEnriched (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool) :
    EnrichedCategory SSet.{u} (SliceObjects.{u} T j right) where
  Hom a b := pathHom ⟨a.val⟩ ⟨b.val⟩
  id a := pathId ⟨a.val⟩
  comp a b c := pathComp ⟨a.val⟩ ⟨b.val⟩ ⟨c.val⟩
  id_comp a b := pathId_comp ⟨a.val⟩ ⟨b.val⟩
  comp_id a b := pathComp_id ⟨a.val⟩ ⟨b.val⟩
  assoc a b c d := pathComp_assoc ⟨a.val⟩ ⟨b.val⟩ ⟨c.val⟩ ⟨d.val⟩

def slice (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool) :
    DaggerModels.SimplicialCat.{u,u} := DaggerModels.SimplicialCat.of (SliceObjects T j right)

/-- Whole enriched inclusion, identity on every original Hom natural transformation. -/
def sliceInclusion (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool) :
    slice.{u} T j right ⟶ NC.{u} T where
  obj a := ⟨a.val⟩
  map _ _ := 𝟙 _
  map_id a := Category.comp_id _
  map_comp a b c := by
    simp only [id_tensorHom_id, Category.comp_id, Category.id_comp]
    rfl

def sliceJoint (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool) :
    SliceObjects.{u} T j right :=
  ⟨ULift.up j, by
    cases right <;> change (ULift.up j : Vertices.{u} T) ≤ ULift.up j <;> exact le_rfl⟩

theorem sliceInclusion_obj (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool)
    (a : (slice.{u} T j right).Obj) : (sliceInclusion T j right).obj a = ⟨a.val⟩ := rfl

theorem sliceInclusion_hom (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool)
    (a b : (slice.{u} T j right).Obj) : (sliceInclusion T j right).map a b = 𝟙 _ := rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
