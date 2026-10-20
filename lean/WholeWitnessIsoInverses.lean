import NativeCellSquareIsoInverse
import WholeWitnessIsoTransport

/-! Actual base-arrow isomorphisms invert whole witness morphisms without changing cells. -/
set_option autoImplicit false
open CategoryTheory
open DaggerSimplexInverseWitnessCategory DaggerNativeCellSquareIsoInverse
universe u v w
namespace DaggerWholeWitnessIsoInverses
noncomputable section
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

def inverse {X Y : Witness R} (e : X.arrow ≅ Y.arrow) (h : X ⟶ Y)
    (he : h.square = e.hom) : Y ⟶ X where
  square := e.inv
  inverse_commutes := by
    let L := R.mapIso (Arrow.leftFunc.mapIso e)
    let T := R.mapIso (Arrow.rightFunc.mapIso e)
    have hh : T.hom ≫ Y.data.inv = X.data.inv ≫ L.hom := by
      simpa only [he] using h.inverse_commutes
    change T.inv ≫ X.data.inv = Y.data.inv ≫ L.inv
    calc
      T.inv ≫ X.data.inv = T.inv ≫ (X.data.inv ≫ L.hom) ≫ L.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = T.inv ≫ (T.hom ≫ Y.data.inv) ≫ L.inv := by rw [← hh]
      _ = Y.data.inv ≫ L.inv := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  triangleLeft := by
    apply triangleSquare_inverse (R.mapIso (Arrow.leftFunc.mapIso e)) X.data.left Y.data.left
    simpa only [he] using h.triangleLeft
  triangleRight := by
    apply triangleSquare_inverse (R.mapIso (Arrow.rightFunc.mapIso e)) X.data.right Y.data.right
    simpa only [he] using h.triangleRight

def iso {X Y : Witness R} (e : X.arrow ≅ Y.arrow) (h : X ⟶ Y)
    (he : h.square = e.hom) : X ≅ Y where
  hom := h
  inv := inverse R e h he
  hom_inv_id := Hom.ext R (by change h.square ≫ e.inv = 𝟙 _; rw [he, e.hom_inv_id])
  inv_hom_id := Hom.ext R (by change e.inv ≫ h.square = 𝟙 _; rw [he, e.inv_hom_id])

def transportedIso (X : Witness R) {a : Arrow C} (e : X.arrow ≅ a) :
    X ≅ DaggerWholeWitnessIsoTransport.witness R X e :=
  iso R e (DaggerWholeWitnessIsoTransport.forward R X e) rfl

end
end DaggerWholeWitnessIsoInverses
