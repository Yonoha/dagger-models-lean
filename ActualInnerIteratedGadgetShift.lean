import ActualInnerIteratedGadgetData
import ActualInnerReplacementExtensions
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Reuse the selected-family shift with the SAME native G; extend full maps to ANY quasi X. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualInnerIteratedGadgetData
open scoped Simplicial
universe u

namespace DaggerActualInnerIteratedGadgetShift
noncomputable section

def shiftCode (P : Code) : Code := ⟨P.base, P.level + 1⟩

/-- The actual original unit is a morphism of the selected endpoint-labelled gadgets. -/
def unitHom (P : Code) : P ⟶ shiftCode P :=
  (⟨DaggerNativeInnerHornFactorization.unit.app (space P), rfl, rfl⟩ : Hom.{u} P (shiftCode P))

/-- Every full original map is carried to its actual F-image; all endpoints are retained. -/
def shiftMap {P Q : Code} (f : P ⟶ Q) : shiftCode P ⟶ shiftCode Q where
  map := DaggerNativeInnerHornFactorization.replacement.map f.map
  first := by
    have h := congrFun (NatTrans.congr_app
      (DaggerNativeInnerHornFactorization.unit.naturality f.map) (op ⦋0⦌)) (alpha P)
    change (DaggerNativeInnerHornFactorization.unit.app (space Q)).app (op ⦋0⦌)
        (f.map.app (op ⦋0⦌) (alpha P)) = _ at h
    rw [f.first] at h
    exact h.symm
  last := by
    have h := congrFun (NatTrans.congr_app
      (DaggerNativeInnerHornFactorization.unit.naturality f.map) (op ⦋0⦌)) (omega P)
    change (DaggerNativeInnerHornFactorization.unit.app (space Q)).app (op ⦋0⦌)
        (f.map.app (op ⦋0⦌) (omega P)) = _ at h
    rw [f.last] at h
    exact h.symm

def shift : Code ⥤ Code where
  obj := shiftCode
  map := shiftMap.{u}
  map_id _ := Hom.ext (DaggerNativeInnerHornFactorization.replacement.map_id _)
  map_comp f g := Hom.ext (DaggerNativeInnerHornFactorization.replacement.map_comp f.map g.map)

def codeUnit : 𝟭 Code ⟶ shift.{u} where
  app := unitHom
  naturality {P Q} f := by
    apply Hom.ext
    change f.map ≫ DaggerNativeInnerHornFactorization.unit.app (space Q) =
      DaggerNativeInnerHornFactorization.unit.app (space P) ≫
        DaggerNativeInnerHornFactorization.replacement.map f.map
    exact DaggerNativeInnerHornFactorization.unit.naturality f.map

variable (X : SSet.{u}) (r : DaggerNativeInnerHornFactorization.replacement.obj X ⟶ X)
variable (hr : DaggerNativeInnerHornFactorization.unit.app X ≫ r = 𝟙 X)
variable (a b : X.obj (op ⦋0⦌))

def overObj (P : Over X a b) : Over X a b where
  code := shiftCode P.code
  map := DaggerActualInnerReplacementExtensions.extension r P.map
  first := by
    have h := congrFun (NatTrans.congr_app
      (DaggerActualInnerReplacementExtensions.unit_extension r hr P.map) (op ⦋0⦌))
      (alpha P.code)
    exact h.trans P.first
  last := by
    have h := congrFun (NatTrans.congr_app
      (DaggerActualInnerReplacementExtensions.unit_extension r hr P.map) (op ⦋0⦌))
      (omega P.code)
    exact h.trans P.last

def over : Over X a b ⥤ Over X a b where
  obj := overObj X r hr a b
  map {P Q} f := ⟨shiftMap f.hom, by
    change DaggerNativeInnerHornFactorization.replacement.map f.hom.map ≫
      DaggerActualInnerReplacementExtensions.extension r Q.map = _
    rw [DaggerActualInnerReplacementExtensions.extension_naturality, f.w]
    rfl⟩
  map_id P := by apply Over.Hom.ext; exact shift.map_id P.code
  map_comp f g := by apply Over.Hom.ext; exact shift.map_comp f.hom g.hom

def overUnit : 𝟭 (Over X a b) ⟶ over X r hr a b where
  app P := ⟨unitHom P.code, by
    change DaggerNativeInnerHornFactorization.unit.app (space P.code) ≫
      DaggerActualInnerReplacementExtensions.extension r P.map = P.map
    exact DaggerActualInnerReplacementExtensions.unit_extension r hr P.map⟩
  naturality {P Q} f := by
    apply Over.Hom.ext
    exact codeUnit.naturality f.hom

def positive : ObjectProperty (Over X a b) := fun P ↦ 0 < P.code.level

abbrev FibrantOver := (positive X a b).FullSubcategory

def inclusion : FibrantOver X a b ⥤ Over X a b := (positive X a b).ι

def toFibrant : Over X a b ⥤ FibrantOver X a b :=
  (positive X a b).lift (over X r hr a b) (fun _ ↦ Nat.succ_pos _)

def allUnit : 𝟭 (Over X a b) ⟶ toFibrant X r hr a b ⋙ inclusion X a b :=
  overUnit X r hr a b

def fibrantUnit : 𝟭 (FibrantOver X a b) ⟶ inclusion X a b ⋙ toFibrant X r hr a b where
  app P := ObjectProperty.homMk ((overUnit X r hr a b).app P.obj)
  naturality {P Q} f := by
    apply ObjectProperty.hom_ext
    exact (overUnit X r hr a b).naturality f.hom

end
end DaggerActualInnerIteratedGadgetShift
