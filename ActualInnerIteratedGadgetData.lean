import ActualNecklaceConeGadgets
import NativeInnerHornFactorization

/-! Reuse the original small-family construction with the SAME native inner-horn replacement.
The old N R Rig family remains separate; every original base space and endpoint is retained. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerNativeInnerHornFactorization
universe u

namespace DaggerActualInnerIteratedGadgetData
noncomputable section

abbrev BaseCode := DaggerActualNecklaceConeGadgets.Code
structure Code where
  base : BaseCode
  level : ℕ

def spaceAt (P : BaseCode) (k : ℕ) : SSet.{u} := match k with
  | 0 => DaggerActualNecklaceConeGadgets.space P
  | k + 1 => replacement.obj (spaceAt P k)

def alphaAt (P : BaseCode) (k : ℕ) : (spaceAt.{u} P k).obj (op ⦋0⦌) := match k with
  | 0 => DaggerActualNecklaceConeGadgets.alpha P
  | k + 1 => (DaggerNativeInnerHornFactorization.unit.app (spaceAt P k)).app (op ⦋0⦌)
      (alphaAt P k)

def omegaAt (P : BaseCode) (k : ℕ) : (spaceAt.{u} P k).obj (op ⦋0⦌) := match k with
  | 0 => DaggerActualNecklaceConeGadgets.omega P
  | k + 1 => (DaggerNativeInnerHornFactorization.unit.app (spaceAt P k)).app (op ⦋0⦌)
      (omegaAt P k)

def space (P : Code) : SSet.{u} := spaceAt P.base P.level
def alpha (P : Code) : (space.{u} P).obj (op ⦋0⦌) := alphaAt P.base P.level
def omega (P : Code) : (space.{u} P).obj (op ⦋0⦌) := omegaAt P.base P.level

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

structure Over (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : Type u where
  code : Code
  map : space code ⟶ X
  first : map.app _ (alpha code) = a
  last : map.app _ (omega code) = b

namespace Over
variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

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
  id_comp f := Hom.ext (DaggerActualInnerIteratedGadgetData.Hom.ext (Category.id_comp f.hom.map))
  comp_id f := Hom.ext (DaggerActualInnerIteratedGadgetData.Hom.ext (Category.comp_id f.hom.map))
  assoc f g h := Hom.ext
    (DaggerActualInnerIteratedGadgetData.Hom.ext (Category.assoc f.hom.map g.hom.map h.hom.map))
end Over

end
end DaggerActualInnerIteratedGadgetData
