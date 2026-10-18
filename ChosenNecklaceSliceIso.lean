import ChosenNecklaceSliceIntervals
import ChosenEnrichedSpecifiedIso

open CategoryTheory EnrichedCategory MonoidalCategory

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

variable (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool)

/-- Specified original interval objects and all original Hom inverses, including both casts. -/
def sideIsoData : SpecifiedEnrichedIsoData
    (NC.{u} (sideCode T j right)) (slice.{u} T j right) where
  objects := sideObjectEquiv T j right
  homs := sideHomIso T j right
  hom_id := (sideNCMap T j right).map_id
  hom_comp := (sideNCMap T j right).map_comp

/-- Full interval-to-slice iso whose hom is the original interval inclusion. -/
def sideIso : NC.{u} (sideCode T j right) ≅ slice.{u} T j right :=
  (sideIsoData T j right).iso

theorem sideIso_hom : (sideIso.{u} T j right).hom = sideNCMap T j right := rfl

theorem sideIso_hom_map (a b : (NC.{u} (sideCode T j right)).Obj) :
    (sideIso T j right).hom.map a b = (sideHomIso T j right a b).hom := rfl

theorem sideIso_inv_map (a b : (slice.{u} T j right).Obj) :
    (sideIso T j right).inv.map a b =
      ((sideIsoData T j right).inverseForwardHom a b).inv := rfl

theorem sideIso_hom_inv : (sideIso.{u} T j right).hom ≫ (sideIso T j right).inv = 𝟙 _ :=
  (sideIso T j right).hom_inv_id

theorem sideIso_inv_hom : (sideIso.{u} T j right).inv ≫ (sideIso T j right).hom = 𝟙 _ :=
  (sideIso T j right).inv_hom_id

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
