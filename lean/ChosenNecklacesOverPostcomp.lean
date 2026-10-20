import ChosenNecklacesOverWedge

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklacesOver

noncomputable section

open NecklaceCode

variable {X Y : SSet.{u}} {a b c : X.obj (op ⦋0⦌)}

/-- Same point code and original vertex map after postcomposition. -/
def postcompPointHom (f : X ⟶ Y) (a : X.obj (op ⦋0⦌)) :
    Hom ((postcomp f).obj (point a)) (point (f.app _ a)) where
  hom := NecklaceCode.Hom.id NecklaceCode.point
  w := by
    change 𝟙 (Δ[0]) ≫ SSet.yonedaEquiv.symm (f.app _ a) = SSet.yonedaEquiv.symm a ≫ f
    rw [Category.id_comp]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply,
      SSet.yonedaEquiv.apply_symm_apply]

/-- Full original wedge comparison, characterized by both unchanged over-Y legs. -/
def postcompWedgeHom (f : X ⟶ Y) (P : NecklacesOver X a b) (Q : NecklacesOver X b c) :
    Hom ((postcomp f).obj (wedge P Q)) (wedge ((postcomp f).obj P) ((postcomp f).obj Q)) where
  hom := NecklaceCode.Hom.id (NecklaceCode.wedge P.code Q.code)
  w := by
    change 𝟙 _ ≫ (wedge ((postcomp f).obj P) ((postcomp f).obj Q)).map =
      (wedge P Q).map ≫ f
    rw [Category.id_comp]
    apply (wedgeIsPushout P.code Q.code).hom_ext
    · change wedgeιLeft P.code Q.code ≫
        (wedge ((postcomp f).obj P) ((postcomp f).obj Q)).map =
      wedgeιLeft P.code Q.code ≫ (wedge P Q).map ≫ f
      dsimp only [wedge, postcomp]
      rw [wedgeDesc_left, ← Category.assoc, wedgeDesc_left]
    · change wedgeιRight P.code Q.code ≫
        (wedge ((postcomp f).obj P) ((postcomp f).obj Q)).map =
      wedgeιRight P.code Q.code ≫ (wedge P Q).map ≫ f
      dsimp only [wedge, postcomp]
      rw [wedgeDesc_right, ← Category.assoc, wedgeDesc_right]

end

end DaggerChosenRigidificationNecklace.NecklacesOver
