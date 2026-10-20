import NativeBisimplicialBox

/-! External boxes preserve the original isomorphisms in both variables. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialBox
universe u
namespace DaggerNativeBisimplicialBoxIso
noncomputable section

def boxIso {K L A B : SSet.{u}} (e : K ≅ L) (d : A ≅ B) : box K A ≅ box L B where
  hom := boxMap e.hom d.hom
  inv := boxMap e.inv d.inv
  hom_inv_id := by
    rw [← boxMap_comp, e.hom_inv_id, d.hom_inv_id, boxMap_id]
  inv_hom_id := by
    rw [← boxMap_comp, e.inv_hom_id, d.inv_hom_id, boxMap_id]

end
end DaggerNativeBisimplicialBoxIso
