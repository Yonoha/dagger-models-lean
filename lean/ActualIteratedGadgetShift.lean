import ActualIteratedGadgetData
import ActualFibrantGadgetExtensions
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! The actual gadget extension is closed on the small iterated family over a fixed N(D). -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualIteratedGadgetData
open scoped Simplicial
universe u

namespace DaggerActualIteratedGadgetShift
noncomputable section

def shiftCode (P : Code) : Code := ⟨P.base, P.level + 1⟩

/-- The actual original unit is a morphism of the selected endpoint-labelled gadgets. -/
def unitHom (P : Code) : P ⟶ shiftCode P :=
  (⟨DaggerActualFibrantGadgetData.unit.app (space P), rfl, rfl⟩ : Hom.{u} P (shiftCode P))

/-- Every full original map is carried to its actual F-image; all endpoints are retained. -/
def shiftMap {P Q : Code} (f : P ⟶ Q) : shiftCode P ⟶ shiftCode Q where
  map := DaggerActualFibrantGadgetData.gadget.map f.map
  first := by
    have h := congrFun (NatTrans.congr_app
      (DaggerActualFibrantGadgetData.unit.naturality f.map) (op ⦋0⦌)) (alpha P)
    change (DaggerActualFibrantGadgetData.unit.app (space Q)).app (op ⦋0⦌)
        (f.map.app (op ⦋0⦌) (alpha P)) = _ at h
    rw [f.first] at h
    exact h.symm
  last := by
    have h := congrFun (NatTrans.congr_app
      (DaggerActualFibrantGadgetData.unit.naturality f.map) (op ⦋0⦌)) (omega P)
    change (DaggerActualFibrantGadgetData.unit.app (space Q)).app (op ⦋0⦌)
        (f.map.app (op ⦋0⦌) (omega P)) = _ at h
    rw [f.last] at h
    exact h.symm

def shift : Code ⥤ Code where
  obj := shiftCode
  map := shiftMap.{u}
  map_id _ := Hom.ext (DaggerActualFibrantGadgetData.gadget.map_id _)
  map_comp f g := Hom.ext (DaggerActualFibrantGadgetData.gadget.map_comp f.map g.map)

def codeUnit : 𝟭 Code ⟶ shift.{u} where
  app := unitHom
  naturality {P Q} f := by
    apply Hom.ext
    change f.map ≫ DaggerActualFibrantGadgetData.unit.app (space Q) =
      DaggerActualFibrantGadgetData.unit.app (space P) ≫
        DaggerActualFibrantGadgetData.gadget.map f.map
    exact DaggerActualFibrantGadgetData.unit.naturality f.map

variable (D : SimplicialCat.{u, u}) (r : OriginalOrdinaryLocalKanReplacement.replacement.obj D ⟶ D)
variable (hr : OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D)
variable (a b : (coherentNerve.obj D).obj (op ⦋0⦌))

/-- The object extension keeps the entire original map and both original endpoint equations. -/
def overObj (P : Over (coherentNerve.obj D) a b) : Over (coherentNerve.obj D) a b where
  code := shiftCode P.code
  map := DaggerActualFibrantGadgetData.extension D r P.map
  first := by
    have h := congrFun (NatTrans.congr_app
      (DaggerActualFibrantGadgetExtensions.unit_extension D r hr P.map) (op ⦋0⦌))
        (alpha P.code)
    exact h.trans P.first
  last := by
    have h := congrFun (NatTrans.congr_app
      (DaggerActualFibrantGadgetExtensions.unit_extension D r hr P.map) (op ⦋0⦌))
        (omega P.code)
    exact h.trans P.last

def over : Over (coherentNerve.obj D) a b ⥤ Over (coherentNerve.obj D) a b where
  obj := overObj D r hr a b
  map {P Q} f := ⟨shiftMap f.hom, by
    change DaggerActualFibrantGadgetData.gadget.map f.hom.map ≫
      DaggerActualFibrantGadgetData.extension D r Q.map = _
    rw [DaggerActualFibrantGadgetExtensions.extension_naturality, f.w]
    rfl⟩
  map_id P := by apply Over.Hom.ext; exact shift.map_id P.code
  map_comp f g := by apply Over.Hom.ext; exact shift.map_comp f.hom g.hom

def overUnit : 𝟭 (Over (coherentNerve.obj D) a b) ⟶ over D r hr a b where
  app P := ⟨unitHom P.code, by
    change DaggerActualFibrantGadgetData.unit.app (space P.code) ≫
      DaggerActualFibrantGadgetData.extension D r P.map = P.map
    exact DaggerActualFibrantGadgetExtensions.unit_extension D r hr P.map⟩
  naturality {P Q} f := by
    apply Over.Hom.ext
    exact codeUnit.naturality f.hom

/-- The full subcategory contains precisely the positive levels of the same small family. -/
def positive : ObjectProperty (Over (coherentNerve.obj D) a b) := fun P ↦ 0 < P.code.level

abbrev FibrantOver := (positive D a b).FullSubcategory

def inclusion : FibrantOver D a b ⥤ Over (coherentNerve.obj D) a b :=
  (positive D a b).ι

/-- The actual extension lands in positive levels without enlarging the source universe. -/
def toFibrant : Over (coherentNerve.obj D) a b ⥤ FibrantOver D a b :=
  (positive D a b).lift (over D r hr a b) (fun _ ↦ Nat.succ_pos _)

def allUnit : 𝟭 (Over (coherentNerve.obj D) a b) ⟶
    toFibrant D r hr a b ⋙ inclusion D a b := overUnit D r hr a b

def fibrantUnit : 𝟭 (FibrantOver D a b) ⟶ inclusion D a b ⋙ toFibrant D r hr a b where
  app P := ObjectProperty.homMk ((overUnit D r hr a b).app P.obj)
  naturality {P Q} f := by
    apply ObjectProperty.hom_ext
    exact (overUnit D r hr a b).naturality f.hom

end
end DaggerActualIteratedGadgetShift
