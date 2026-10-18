import ChosenNecklacesOver
import OriginalCounitRightCone
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! A common category containing the original necklaces and collapsed-face cones.
All endpoint-preserving simplicial maps are allowed as morphisms. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
universe u

namespace DaggerActualNecklaceConeGadgets
noncomputable section

abbrev Code := NecklaceCode ⊕ ℕ

def space (P : Code) : SSet.{u} := match P with
  | Sum.inl T => T.toSSet
  | Sum.inr n => DaggerOriginalCounitRightCone.cone n

def alpha (P : Code) : (space.{u} P).obj (op ⦋0⦌) := match P with
  | Sum.inl T => T.first
  | Sum.inr n => DaggerOriginalCounitRightCone.alpha n

def omega (P : Code) : (space.{u} P).obj (op ⦋0⦌) := match P with
  | Sum.inl T => T.last
  | Sum.inr n => DaggerOriginalCounitRightCone.omega n

structure Hom (P Q : Code) where
  map : space.{u} P ⟶ space Q
  first : map.app _ (alpha P) = alpha Q
  last : map.app _ (omega P) = omega Q

namespace Hom
@[ext] theorem ext {P Q : Code} {f g : Hom.{u} P Q} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (P : Code) : Hom.{u} P P := ⟨𝟙 _, rfl, rfl⟩

def comp {P Q R : Code} (f : Hom.{u} P Q) (g : Hom Q R) : Hom P R where
  map := f.map ≫ g.map
  first := by change g.map.app _ (f.map.app _ (alpha P)) = _; rw [f.first, g.first]
  last := by change g.map.app _ (f.map.app _ (omega P)) = _; rw [f.last, g.last]
end Hom

instance : Category.{u} Code where
  Hom := Hom.{u}
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.map)
  comp_id f := Hom.ext (Category.comp_id f.map)
  assoc f g h := Hom.ext (Category.assoc f.map g.map h.map)

def necklace : NecklaceCode ⥤ Code where
  obj T := .inl T
  map f := ⟨f.map, f.first, f.last⟩

structure Over (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : Type u where
  code : Code
  map : space code ⟶ X
  first : map.app _ (alpha code) = a
  last : map.app _ (omega code) = b

namespace Over
variable {X Y : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

structure Hom (P Q : Over X a b) where
  hom : P.code ⟶ Q.code
  w : hom.map ≫ Q.map = P.map

namespace Hom
@[ext] theorem ext {P Q : Over X a b} {f g : Hom P Q} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl
def id (P : Over X a b) : Hom P P := ⟨𝟙 _, Category.id_comp _⟩
def comp {P Q R : Over X a b} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := f.hom ≫ g.hom
  w := by change (f.hom.map ≫ g.hom.map) ≫ R.map = _; rw [Category.assoc, g.w, f.w]
end Hom

instance : Category (Over X a b) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (DaggerActualNecklaceConeGadgets.Hom.ext (Category.id_comp f.hom.map))
  comp_id f := Hom.ext (DaggerActualNecklaceConeGadgets.Hom.ext (Category.comp_id f.hom.map))
  assoc f g h := Hom.ext
    (DaggerActualNecklaceConeGadgets.Hom.ext (Category.assoc f.hom.map g.hom.map h.hom.map))

def postcomp (f : X ⟶ Y) : Over X a b ⥤ Over Y (f.app _ a) (f.app _ b) where
  obj P := ⟨P.code, P.map ≫ f, by
    change f.app _ (P.map.app _ (alpha P.code)) = _; rw [P.first], by
    change f.app _ (P.map.app _ (omega P.code)) = _; rw [P.last]⟩
  map h := ⟨h.hom, by rw [← Category.assoc, h.w]⟩
end Over

def inclusion (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    NecklacesOver X a b ⥤ Over X a b where
  obj P := ⟨.inl P.code, P.map, P.first, P.last⟩
  map h := ⟨⟨h.hom.map, h.hom.first, h.hom.last⟩, h.w⟩

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (Q : Over X a b)

abbrev Comma := CostructuredArrow (inclusion X a b) Q

def commaToNecklaces : Comma Q ⥤ NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code)
    where
  obj P := ⟨P.left.code, P.hom.hom.map, P.hom.hom.first, P.hom.hom.last⟩
  map {P R} h := ⟨h.left.hom, by
    exact congrArg (fun f : (inclusion X a b).obj P.left ⟶ Q ↦ f.hom.map)
      (CostructuredArrow.w h)⟩

def necklaceOverObj (P : NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code)) :
    NecklacesOver X a b where
  code := P.code
  map := P.map ≫ Q.map
  first := by change Q.map.app _ (P.map.app _ P.code.first) = a; rw [P.first, Q.first]
  last := by change Q.map.app _ (P.map.app _ P.code.last) = b; rw [P.last, Q.last]

def necklacesToComma : NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code) ⥤ Comma Q
    where
  obj P := CostructuredArrow.mk
    (⟨⟨P.map, P.first, P.last⟩, rfl⟩ : (inclusion X a b).obj (necklaceOverObj Q P) ⟶ Q)
  map {P R} h := CostructuredArrow.homMk
    (⟨h.hom, by
      change h.hom.map ≫ (R.map ≫ Q.map) = _
      rw [← Category.assoc, h.w]
      rfl⟩ :
      necklaceOverObj Q P ⟶ necklaceOverObj Q R)
    (by
      apply Over.Hom.ext
      apply Hom.ext
      exact h.w)
  map_id P := by apply CostructuredArrow.hom_ext; apply NecklacesOver.Hom.ext; rfl
  map_comp h k := by apply CostructuredArrow.hom_ext; apply NecklacesOver.Hom.ext; rfl

theorem comma_original_map (P : Comma Q) :
    ((commaToNecklaces Q).obj P).map ≫ Q.map = P.left.map := P.hom.w

def necklaceRoundtrip : necklacesToComma Q ⋙ commaToNecklaces Q ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ Iso.refl P) (by
    intro P R h
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change h.hom.map ≫ 𝟙 _ = 𝟙 _ ≫ h.hom.map
    simp)

def commaLeftRoundtripIso (P : Comma Q) :
    ((necklacesToComma Q).obj ((commaToNecklaces Q).obj P)).left ≅ P.left where
  hom := ⟨𝟙 P.left.code, by
    change 𝟙 _ ≫ P.left.map = P.hom.hom.map ≫ Q.map
    rw [Category.id_comp]
    exact P.hom.w.symm⟩
  inv := ⟨𝟙 P.left.code, by
    change 𝟙 _ ≫ (P.hom.hom.map ≫ Q.map) = P.left.map
    rw [Category.id_comp]
    exact P.hom.w⟩
  hom_inv_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 P.left.code.toSSet ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 P.left.code.toSSet ≫ 𝟙 _ = 𝟙 _
    simp

def commaRoundtrip : commaToNecklaces Q ⋙ necklacesToComma Q ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ CostructuredArrow.isoMk (commaLeftRoundtripIso Q P) (by
    apply Over.Hom.ext
    apply Hom.ext
    change 𝟙 _ ≫ P.hom.hom.map = P.hom.hom.map
    exact Category.id_comp _)) (by
    intro P R h
    apply CostructuredArrow.hom_ext
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change h.left.hom.map ≫ 𝟙 _ = 𝟙 _ ≫ h.left.hom.map
    simp)

/-- The whole actual comma category retains the original gadget map and both endpoints. -/
def commaEquivalence : Comma Q ≌ NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code) :=
  CategoryTheory.Equivalence.mk (commaToNecklaces Q) (necklacesToComma Q)
    (commaRoundtrip Q).symm (necklaceRoundtrip Q)

end
end DaggerActualNecklaceConeGadgets
