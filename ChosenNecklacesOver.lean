import ChosenNecklaceFlags

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

/-- Actual necklaces over the same original simplicial set, with both endpoint equations. -/
structure NecklacesOver (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : Type u where
  code : NecklaceCode
  map : code.toSSet ⟶ X
  first : map.app _ code.first = a
  last : map.app _ code.last = b

namespace NecklacesOver

variable {X Y Z : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- Every original endpoint-preserving over-X map is included. -/
structure Hom (P Q : NecklacesOver X a b) where
  hom : NecklaceCode.Hom.{u} P.code Q.code
  w : hom.map ≫ Q.map = P.map

namespace Hom

@[ext] theorem ext {P Q : NecklacesOver X a b} {f g : Hom P Q}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (P : NecklacesOver X a b) : Hom P P where
  hom := NecklaceCode.Hom.id P.code
  w := Category.id_comp _

def comp {P Q R : NecklacesOver X a b} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := NecklaceCode.Hom.comp f.hom g.hom
  w := by
    change (f.hom.map ≫ g.hom.map) ≫ R.map = P.map
    rw [Category.assoc, g.w, f.w]

end Hom

instance category : Category (NecklacesOver X a b) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (NecklaceCode.Hom.ext (Category.id_comp f.hom.map))
  comp_id f := Hom.ext (NecklaceCode.Hom.ext (Category.comp_id f.hom.map))
  assoc f g h := Hom.ext (NecklaceCode.Hom.ext
    (Category.assoc f.hom.map g.hom.map h.hom.map))

def forget (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : NecklacesOver X a b ⥤ NecklaceCode where
  obj := code
  map f := f.hom

/-- Postcompose the original maps. The code, all flags and actual endpoints are retained. -/
def postcomp (f : X ⟶ Y) : NecklacesOver X a b ⥤ NecklacesOver Y (f.app _ a) (f.app _ b) where
  obj P :=
    { code := P.code
      map := P.map ≫ f
      first := by change f.app _ (P.map.app _ P.code.first) = f.app _ a; rw [P.first]
      last := by change f.app _ (P.map.app _ P.code.last) = f.app _ b; rw [P.last] }
  map h :=
    { hom := h.hom
      w := by rw [← Category.assoc, h.w] }

def flagDiagram (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    NecklacesOver X a b ⥤ SSet.{u} := forget X a b ⋙ flagFunctor

theorem map_code (f : X ⟶ Y) (P : NecklacesOver X a b) :
    ((postcomp f).obj P).code = P.code := rfl

theorem map_original (f : X ⟶ Y) (P : NecklacesOver X a b) :
    ((postcomp f).obj P).map = P.map ≫ f := rfl

end NecklacesOver

end

end DaggerChosenRigidificationNecklace
