import ChosenNecklaceTripleWedge

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T U V : NecklaceCode)

def wedgeAssocHom : toSSet.{u} (wedge (wedge T U) V) ⟶ toSSet.{u} (wedge T (wedge U V)) :=
  tripleLeftDesc T U V (tripleRightT T U V) (tripleRightU T U V) (tripleRightV T U V)
    (tripleRight_comm₁ T U V) (tripleRight_comm₂ T U V)

def wedgeAssocInv : toSSet.{u} (wedge T (wedge U V)) ⟶ toSSet.{u} (wedge (wedge T U) V) :=
  tripleRightDesc T U V (tripleLeftT T U V) (tripleLeftU T U V) (tripleLeftV T U V)
    (tripleLeft_comm₁ T U V) (tripleLeft_comm₂ T U V)

theorem wedgeAssocHom_T : tripleLeftT T U V ≫ wedgeAssocHom.{u} T U V =
    tripleRightT T U V := tripleLeftDesc_T _ _ _ _ _ _ _ _

theorem wedgeAssocHom_U : tripleLeftU T U V ≫ wedgeAssocHom.{u} T U V =
    tripleRightU T U V := tripleLeftDesc_U _ _ _ _ _ _ _ _

theorem wedgeAssocHom_V : tripleLeftV T U V ≫ wedgeAssocHom.{u} T U V =
    tripleRightV T U V := tripleLeftDesc_V _ _ _ _ _ _ _ _

theorem wedgeAssocInv_T : tripleRightT T U V ≫ wedgeAssocInv.{u} T U V =
    tripleLeftT T U V := tripleRightDesc_T _ _ _ _ _ _ _ _

theorem wedgeAssocInv_U : tripleRightU T U V ≫ wedgeAssocInv.{u} T U V =
    tripleLeftU T U V := tripleRightDesc_U _ _ _ _ _ _ _ _

theorem wedgeAssocInv_V : tripleRightV T U V ≫ wedgeAssocInv.{u} T U V =
    tripleLeftV T U V := tripleRightDesc_V _ _ _ _ _ _ _ _

/-- Full association iso, characterized by all three original necklace inclusions. -/
def wedgeAssoc : toSSet.{u} (wedge (wedge T U) V) ≅ toSSet.{u} (wedge T (wedge U V)) where
  hom := wedgeAssocHom T U V
  inv := wedgeAssocInv T U V
  hom_inv_id := by
    apply tripleLeft_hom_ext
    · rw [← Category.assoc, wedgeAssocHom_T, wedgeAssocInv_T, Category.comp_id]
    · rw [← Category.assoc, wedgeAssocHom_U, wedgeAssocInv_U, Category.comp_id]
    · rw [← Category.assoc, wedgeAssocHom_V, wedgeAssocInv_V, Category.comp_id]
  inv_hom_id := by
    apply tripleRight_hom_ext
    · rw [← Category.assoc, wedgeAssocInv_T, wedgeAssocHom_T, Category.comp_id]
    · rw [← Category.assoc, wedgeAssocInv_U, wedgeAssocHom_U, Category.comp_id]
    · rw [← Category.assoc, wedgeAssocInv_V, wedgeAssocHom_V, Category.comp_id]

theorem wedgeAssoc_first :
    (wedgeAssoc.{u} T U V).hom.app _ (wedge (wedge T U) V).first =
      (wedge T (wedge U V)).first := by
  have h : pointAt (wedge (wedge T U) V) (ULift.up 0) ≫ wedgeAssocHom T U V =
      pointAt (wedge T (wedge U V)) (ULift.up 0) := by
    rw [← pointAt_first_left (wedge T U) V, ← pointAt_first_left T U]
    simp only [Category.assoc]
    have hl := wedgeAssocHom_T.{u} T U V
    dsimp only [tripleLeftT, tripleRightT] at hl
    rw [Category.assoc] at hl
    rw [hl]
    exact pointAt_first_left T (wedge U V)
  have hh := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, first] using hh

theorem wedgeAssoc_last :
    (wedgeAssoc.{u} T U V).hom.app _ (wedge (wedge T U) V).last =
      (wedge T (wedge U V)).last := by
  have h : pointAt (wedge (wedge T U) V)
      (ULift.up (Fin.last (wedge (wedge T U) V).len)) ≫ wedgeAssocHom T U V =
      pointAt (wedge T (wedge U V))
        (ULift.up (Fin.last (wedge T (wedge U V)).len)) := by
    rw [← pointAt_last_right (wedge T U) V, Category.assoc]
    have hl := wedgeAssocHom_V.{u} T U V
    dsimp only [tripleLeftV] at hl
    rw [hl]
    rw [tripleRightV, ← Category.assoc, pointAt_last_right U V, pointAt_last_right]
  have hh := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, last] using hh

def wedgeAssocCodeHom : NecklaceCode.Hom.{u} (wedge (wedge T U) V) (wedge T (wedge U V)) where
  map := (wedgeAssoc T U V).hom
  first := wedgeAssoc_first T U V
  last := wedgeAssoc_last T U V

end

end DaggerChosenRigidificationNecklace.NecklaceCode
