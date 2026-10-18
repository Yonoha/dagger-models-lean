import ChosenNecklaceWedgeUnits

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T U V : NecklaceCode)

def tripleLeftT : toSSet.{u} T ⟶ toSSet.{u} (wedge (wedge T U) V) :=
  wedgeιLeft T U ≫ wedgeιLeft (wedge T U) V

def tripleLeftU : toSSet.{u} U ⟶ toSSet.{u} (wedge (wedge T U) V) :=
  wedgeιRight T U ≫ wedgeιLeft (wedge T U) V

def tripleLeftV : toSSet.{u} V ⟶ toSSet.{u} (wedge (wedge T U) V) :=
  wedgeιRight (wedge T U) V

def tripleRightT : toSSet.{u} T ⟶ toSSet.{u} (wedge T (wedge U V)) :=
  wedgeιLeft T (wedge U V)

def tripleRightU : toSSet.{u} U ⟶ toSSet.{u} (wedge T (wedge U V)) :=
  wedgeιLeft U V ≫ wedgeιRight T (wedge U V)

def tripleRightV : toSSet.{u} V ⟶ toSSet.{u} (wedge T (wedge U V)) :=
  wedgeιRight U V ≫ wedgeιRight T (wedge U V)

theorem tripleLeft_comm₁ :
    pointAt T (ULift.up (Fin.last T.len)) ≫ tripleLeftT.{u} T U V =
      pointAt U (ULift.up 0) ≫ tripleLeftU T U V := by
  dsimp [tripleLeftT, tripleLeftU]
  rw [← Category.assoc, wedge_comm, Category.assoc]

theorem tripleLeft_comm₂ :
    pointAt U (ULift.up (Fin.last U.len)) ≫ tripleLeftU.{u} T U V =
      pointAt V (ULift.up 0) ≫ tripleLeftV T U V := by
  dsimp [tripleLeftU, tripleLeftV]
  rw [← Category.assoc, pointAt_last_right, wedge_comm]

theorem tripleRight_comm₁ :
    pointAt T (ULift.up (Fin.last T.len)) ≫ tripleRightT.{u} T U V =
      pointAt U (ULift.up 0) ≫ tripleRightU T U V := by
  dsimp [tripleRightT, tripleRightU]
  rw [wedge_comm, ← pointAt_first_left U V, Category.assoc]

theorem tripleRight_comm₂ :
    pointAt U (ULift.up (Fin.last U.len)) ≫ tripleRightU.{u} T U V =
      pointAt V (ULift.up 0) ≫ tripleRightV T U V := by
  dsimp [tripleRightU, tripleRightV]
  rw [← Category.assoc, wedge_comm, Category.assoc]

variable {X : SSet.{u}} (f : toSSet.{u} T ⟶ X) (g : toSSet.{u} U ⟶ X)
  (h : toSSet.{u} V ⟶ X)
  (h₁ : pointAt T (ULift.up (Fin.last T.len)) ≫ f = pointAt U (ULift.up 0) ≫ g)
  (h₂ : pointAt U (ULift.up (Fin.last U.len)) ≫ g = pointAt V (ULift.up 0) ≫ h)

def tripleLeftDesc : toSSet.{u} (wedge (wedge T U) V) ⟶ X :=
  wedgeDesc (wedge T U) V (wedgeDesc T U f g h₁) h (by rw [wedgeDesc_last, h₂])

def tripleRightDesc : toSSet.{u} (wedge T (wedge U V)) ⟶ X :=
  wedgeDesc T (wedge U V) f (wedgeDesc U V g h h₂) (by rw [wedgeDesc_first, h₁])

theorem tripleLeftDesc_T :
    tripleLeftT T U V ≫ tripleLeftDesc T U V f g h h₁ h₂ = f := by
  simp only [tripleLeftT, tripleLeftDesc, Category.assoc, wedgeDesc_left]

theorem tripleLeftDesc_U :
    tripleLeftU T U V ≫ tripleLeftDesc T U V f g h h₁ h₂ = g := by
  simp only [tripleLeftU, tripleLeftDesc, Category.assoc, wedgeDesc_left, wedgeDesc_right]

theorem tripleLeftDesc_V :
    tripleLeftV T U V ≫ tripleLeftDesc T U V f g h h₁ h₂ = h :=
  wedgeDesc_right _ _ _ _ _

theorem tripleRightDesc_T :
    tripleRightT T U V ≫ tripleRightDesc T U V f g h h₁ h₂ = f :=
  wedgeDesc_left _ _ _ _ _

theorem tripleRightDesc_U :
    tripleRightU T U V ≫ tripleRightDesc T U V f g h h₁ h₂ = g := by
  simp only [tripleRightU, tripleRightDesc, Category.assoc, wedgeDesc_right, wedgeDesc_left]

theorem tripleRightDesc_V :
    tripleRightV T U V ≫ tripleRightDesc T U V f g h h₁ h₂ = h := by
  simp only [tripleRightV, tripleRightDesc, Category.assoc, wedgeDesc_right]

variable {T U V}

theorem tripleLeft_hom_ext {k l : toSSet.{u} (wedge (wedge T U) V) ⟶ X}
    (hT : tripleLeftT T U V ≫ k = tripleLeftT T U V ≫ l)
    (hU : tripleLeftU T U V ≫ k = tripleLeftU T U V ≫ l)
    (hV : tripleLeftV T U V ≫ k = tripleLeftV T U V ≫ l) : k = l := by
  apply (wedgeIsPushout (wedge T U) V).hom_ext
  · apply (wedgeIsPushout T U).hom_ext
    · simpa only [tripleLeftT, Category.assoc] using hT
    · simpa only [tripleLeftU, Category.assoc] using hU
  · exact hV

theorem tripleRight_hom_ext {k l : toSSet.{u} (wedge T (wedge U V)) ⟶ X}
    (hT : tripleRightT T U V ≫ k = tripleRightT T U V ≫ l)
    (hU : tripleRightU T U V ≫ k = tripleRightU T U V ≫ l)
    (hV : tripleRightV T U V ≫ k = tripleRightV T U V ≫ l) : k = l := by
  apply (wedgeIsPushout T (wedge U V)).hom_ext
  · exact hT
  · apply (wedgeIsPushout U V).hom_ext
    · simpa only [tripleRightU, Category.assoc] using hU
    · simpa only [tripleRightV, Category.assoc] using hV

end

end DaggerChosenRigidificationNecklace.NecklaceCode
