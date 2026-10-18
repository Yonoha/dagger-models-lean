import ChosenNecklaceWedgeAssoc

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable {T U T' U' V : NecklaceCode}

theorem pointAt_first_comp (f : NecklaceCode.Hom.{u} T U) :
    pointAt T (ULift.up 0) ≫ f.map = pointAt U (ULift.up 0) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, pointAt_vertex, pointAt_vertex]
  exact f.first

theorem pointAt_last_comp (f : NecklaceCode.Hom.{u} T U) :
    pointAt T (ULift.up (Fin.last T.len)) ≫ f.map =
      pointAt U (ULift.up (Fin.last U.len)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, pointAt_vertex, pointAt_vertex]
  exact f.last

theorem first_of_point (f : toSSet.{u} T ⟶ toSSet.{u} U)
    (h : pointAt T (ULift.up 0) ≫ f = pointAt U (ULift.up 0)) :
    f.app _ T.first = U.first := by
  have hh := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, first] using hh

theorem last_of_point (f : toSSet.{u} T ⟶ toSSet.{u} U)
    (h : pointAt T (ULift.up (Fin.last T.len)) ≫ f =
      pointAt U (ULift.up (Fin.last U.len))) : f.app _ T.last = U.last := by
  have hh := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, last] using hh

def wedgeMap (f : NecklaceCode.Hom.{u} T T') (g : NecklaceCode.Hom.{u} U U') :
    NecklaceCode.Hom.{u} (wedge T U) (wedge T' U') where
  map := wedgeDesc T U (f.map ≫ wedgeιLeft T' U') (g.map ≫ wedgeιRight T' U') (by
    rw [← Category.assoc, pointAt_last_comp, wedge_comm, ← pointAt_first_comp g]
    rw [Category.assoc])
  first := first_of_point _ (by
    rw [wedgeDesc_first, ← Category.assoc, pointAt_first_comp, pointAt_first_left])
  last := last_of_point _ (by
    rw [wedgeDesc_last, ← Category.assoc, pointAt_last_comp, pointAt_last_right])

theorem wedgeMap_left (f : NecklaceCode.Hom.{u} T T') (g : NecklaceCode.Hom.{u} U U') :
    wedgeιLeft T U ≫ (wedgeMap f g).map = f.map ≫ wedgeιLeft T' U' :=
  wedgeDesc_left _ _ _ _ _

theorem wedgeMap_right (f : NecklaceCode.Hom.{u} T T') (g : NecklaceCode.Hom.{u} U U') :
    wedgeιRight T U ≫ (wedgeMap f g).map = g.map ≫ wedgeιRight T' U' :=
  wedgeDesc_right _ _ _ _ _

theorem wedgeMap_id :
    wedgeMap (Hom.id.{u} T) (Hom.id.{u} U) = Hom.id (wedge T U) := by
  apply Hom.ext
  apply (wedgeIsPushout T U).hom_ext
  · rw [wedgeMap_left]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rw [wedgeMap_right]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

variable {T'' U'' : NecklaceCode}

theorem wedgeMap_comp (f : Hom.{u} T T') (g : Hom.{u} U U')
    (f' : Hom.{u} T' T'') (g' : Hom.{u} U' U'') :
    wedgeMap (Hom.comp f f') (Hom.comp g g') = Hom.comp (wedgeMap f g) (wedgeMap f' g') := by
  apply Hom.ext
  apply (wedgeIsPushout T U).hom_ext
  · change wedgeιLeft T U ≫ (wedgeMap (Hom.comp f f') (Hom.comp g g')).map =
      wedgeιLeft T U ≫ (wedgeMap f g).map ≫ (wedgeMap f' g').map
    rw [wedgeMap_left, ← Category.assoc, wedgeMap_left, Category.assoc, wedgeMap_left]
    exact Category.assoc _ _ _
  · change wedgeιRight T U ≫ (wedgeMap (Hom.comp f f') (Hom.comp g g')).map =
      wedgeιRight T U ≫ (wedgeMap f g).map ≫ (wedgeMap f' g').map
    rw [wedgeMap_right, ← Category.assoc, wedgeMap_right, Category.assoc, wedgeMap_right]
    exact Category.assoc _ _ _

end

end DaggerChosenRigidificationNecklace.NecklaceCode
