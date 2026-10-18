import ChosenNecklacesOver
import ChosenNecklaceWedgeFlags
import ChosenNecklaceUnitCodeMaps

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklacesOver

noncomputable section

open NecklaceCode

variable {X : SSet.{u}} {a b c d : X.obj (op ⦋0⦌)}

/-- The literal point necklace at the supplied original vertex. -/
def point (a : X.obj (op ⦋0⦌)) : NecklacesOver X a a where
  code := NecklaceCode.point
  map := SSet.yonedaEquiv.symm a
  first := pointAt_vertex_apply a _
  last := pointAt_vertex_apply a _

theorem wedge_compat (P : NecklacesOver X a b) (Q : NecklacesOver X b c) :
    pointAt P.code (ULift.up (Fin.last P.code.len)) ≫ P.map =
      pointAt Q.code (ULift.up 0) ≫ Q.map := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, pointAt_vertex, pointAt_vertex]
  exact P.last.trans Q.first.symm

def wedge (P : NecklacesOver X a b) (Q : NecklacesOver X b c) : NecklacesOver X a c where
  code := NecklaceCode.wedge P.code Q.code
  map := wedgeDesc P.code Q.code P.map Q.map (wedge_compat P Q)
  first := by
    have h := congrArg SSet.yonedaEquiv
      (wedgeDesc_first P.code Q.code P.map Q.map (wedge_compat P Q))
    simp only [SSet.yonedaEquiv_comp, pointAt_vertex] at h
    exact h.trans P.first
  last := by
    have h := congrArg SSet.yonedaEquiv
      (wedgeDesc_last P.code Q.code P.map Q.map (wedge_compat P Q))
    simp only [SSet.yonedaEquiv_comp, pointAt_vertex] at h
    exact h.trans Q.last

theorem wedge_left (P : NecklacesOver X a b) (Q : NecklacesOver X b c) :
    wedgeιLeft P.code Q.code ≫ (wedge P Q).map = P.map :=
  wedgeDesc_left _ _ _ _ _

theorem wedge_right (P : NecklacesOver X a b) (Q : NecklacesOver X b c) :
    wedgeιRight P.code Q.code ≫ (wedge P Q).map = Q.map :=
  wedgeDesc_right _ _ _ _ _

def wedgeHom {P P' : NecklacesOver X a b} {Q Q' : NecklacesOver X b c}
    (f : Hom P P') (g : Hom Q Q') : Hom (wedge P Q) (wedge P' Q') where
  hom := wedgeMap f.hom g.hom
  w := by
    apply (wedgeIsPushout P.code Q.code).hom_ext
    · rw [← Category.assoc, wedgeMap_left, Category.assoc, wedge_left, f.w, wedge_left]
    · rw [← Category.assoc, wedgeMap_right, Category.assoc, wedge_right, g.w, wedge_right]

/-- Full association arrow over the same original X, not merely a code relabelling. -/
def wedgeAssocOver (P : NecklacesOver X a b) (Q : NecklacesOver X b c)
    (R : NecklacesOver X c d) : Hom (wedge (wedge P Q) R) (wedge P (wedge Q R)) where
  hom := wedgeAssocCodeHom P.code Q.code R.code
  w := by
    apply tripleLeft_hom_ext
    · change tripleLeftT P.code Q.code R.code ≫
        wedgeAssocHom P.code Q.code R.code ≫ (wedge P (wedge Q R)).map = _
      rw [← Category.assoc, wedgeAssocHom_T]
      dsimp only [tripleRightT, tripleLeftT]
      dsimp only [wedge]
      simp only [Category.assoc, wedgeDesc_left]
    · change tripleLeftU P.code Q.code R.code ≫
        wedgeAssocHom P.code Q.code R.code ≫ (wedge P (wedge Q R)).map = _
      rw [← Category.assoc, wedgeAssocHom_U]
      dsimp only [tripleRightU, tripleLeftU]
      dsimp only [wedge]
      simp only [Category.assoc, wedgeDesc_right, wedgeDesc_left]
    · change tripleLeftV P.code Q.code R.code ≫
        wedgeAssocHom P.code Q.code R.code ≫ (wedge P (wedge Q R)).map = _
      rw [← Category.assoc, wedgeAssocHom_V]
      dsimp only [tripleRightV, tripleLeftV]
      dsimp only [wedge]
      simp only [Category.assoc, wedgeDesc_right]

def wedgeLeftUnitOver (P : NecklacesOver X a b) : Hom (wedge (point a) P) P where
  hom := wedgeLeftUnitCode P.code
  w := by
    apply (wedgeIsPushout NecklaceCode.point P.code).hom_ext
    · dsimp only [wedgeLeftUnitCode]
      rw [← Category.assoc, wedgeLeftUnit_point]
      dsimp only [point, wedge]
      rw [wedgeDesc_left]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, pointAt_vertex, SSet.yonedaEquiv.apply_symm_apply]
      exact P.first
    · rw [← Category.assoc]
      change (wedgeLeftUnit P.code).inv ≫ (wedgeLeftUnit P.code).hom ≫ P.map = _
      rw [Iso.inv_hom_id_assoc]
      exact (wedge_right (point a) P).symm

def wedgeRightUnitOver (P : NecklacesOver X a b) : Hom (wedge P (point b)) P where
  hom := wedgeRightUnitCode P.code
  w := by
    apply (wedgeIsPushout P.code NecklaceCode.point).hom_ext
    · rw [← Category.assoc]
      change (wedgeRightUnit P.code).inv ≫ (wedgeRightUnit P.code).hom ≫ P.map = _
      rw [Iso.inv_hom_id_assoc]
      exact (wedge_left P (point b)).symm
    · dsimp only [wedgeRightUnitCode]
      rw [← Category.assoc, wedgeRightUnit_point]
      dsimp only [point, wedge]
      rw [wedgeDesc_right]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, pointAt_vertex, SSet.yonedaEquiv.apply_symm_apply]
      exact P.last

end

end DaggerChosenRigidificationNecklace.NecklacesOver
