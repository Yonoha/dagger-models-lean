import ChosenNecklaceOrderMaps
import ChosenNecklaceBeadCoordinates

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

def first (T : NecklaceCode) : (toSSet.{u} T).obj (op ⦋0⦌) :=
  T.verticesEquiv.symm (ULift.up 0)

def last (T : NecklaceCode) : (toSSet.{u} T).obj (op ⦋0⦌) :=
  T.verticesEquiv.symm (ULift.up (Fin.last T.len))

/-- All actual endpoint-preserving simplicial maps, including collapsed bead maps. -/
structure Hom (T U : NecklaceCode) where
  map : toSSet.{u} T ⟶ toSSet.{u} U
  first : map.app _ T.first = U.first
  last : map.app _ T.last = U.last

namespace Hom

@[ext] theorem ext {T U : NecklaceCode} {f g : Hom.{u} T U} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (T : NecklaceCode) : Hom.{u} T T where
  map := 𝟙 _
  first := rfl
  last := rfl

def comp {T U V : NecklaceCode} (f : Hom.{u} T U) (g : Hom.{u} U V) : Hom.{u} T V where
  map := f.map ≫ g.map
  first := by change g.map.app _ (f.map.app _ T.first) = V.first; rw [f.first, g.first]
  last := by change g.map.app _ (f.map.app _ T.last) = V.last; rw [f.last, g.last]

end Hom

instance category : Category.{u} NecklaceCode where
  Hom := Hom.{u}
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.map)
  comp_id f := Hom.ext (Category.comp_id f.map)
  assoc f g h := Hom.ext (Category.assoc f.map g.map h.map)

def simplicialFunctor : NecklaceCode ⥤ SSet.{u} where
  obj T := T.toSSet
  map f := f.map

theorem orderMap_first {T U : NecklaceCode} (f : Hom.{u} T U) :
    orderMap f.map 0 = 0 := by
  change (U.verticesEquiv (f.map.app _ T.first)).down = 0
  rw [f.first]
  exact congrArg ULift.down (U.verticesEquiv.apply_symm_apply (ULift.up 0))

theorem orderMap_last {T U : NecklaceCode} (f : Hom.{u} T U) :
    orderMap f.map (Fin.last T.len) = Fin.last U.len := by
  change (U.verticesEquiv (f.map.app _ T.last)).down = Fin.last U.len
  rw [f.last]
  exact congrArg ULift.down (U.verticesEquiv.apply_symm_apply (ULift.up (Fin.last U.len)))

end

end DaggerChosenRigidificationNecklace.NecklaceCode
