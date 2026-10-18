import OriginalGadgetProduct
import OriginalGadgetProductProjection

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X Y : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {c d : Y.obj (op ⦋0⦌)}

theorem theta_obj_fst (P : GadgetsOver X a b × GadgetsOver Y c d) :
    (theta.obj P).obj.hom ≫ fst X Y =
      (tensorProjectionLeft P.1.obj.left P.2.obj.left).map ≫ P.1.obj.hom := by
  have hf : (P.1.obj.hom ⊗ₘ P.2.obj.hom) ≫ fst X Y =
      fst P.1.obj.left.space P.2.obj.left.space ≫ P.1.obj.hom :=
    CartesianMonoidalCategory.tensorHom_fst P.1.obj.hom P.2.obj.hom
  change ((tensorSpaceIso _ _).hom ≫ (P.1.obj.hom ⊗ₘ P.2.obj.hom)) ≫ fst X Y =
    tensorLeftMap _ _ ≫ P.1.obj.hom
  rw [Category.assoc, hf,
    ← Category.assoc, tensorSpaceIso_hom_fst]

theorem theta_obj_snd (P : GadgetsOver X a b × GadgetsOver Y c d) :
    (theta.obj P).obj.hom ≫ snd X Y =
      (tensorProjectionRight P.1.obj.left P.2.obj.left).map ≫ P.2.obj.hom := by
  have hf : (P.1.obj.hom ⊗ₘ P.2.obj.hom) ≫ snd X Y =
      snd P.1.obj.left.space P.2.obj.left.space ≫ P.2.obj.hom :=
    CartesianMonoidalCategory.tensorHom_snd P.1.obj.hom P.2.obj.hom
  change ((tensorSpaceIso _ _).hom ≫ (P.1.obj.hom ⊗ₘ P.2.obj.hom)) ≫ snd X Y =
    tensorRightMap _ _ ≫ P.2.obj.hom
  rw [Category.assoc, hf,
    ← Category.assoc, tensorSpaceIso_hom_snd]

theorem tensorDiagonal_map_left (P : Code.{u}) :
    (tensorDiagonal P).map ≫ (tensorProjectionLeft P P).map = 𝟙 P.space :=
  congrArg (fun f : P ⟶ P ↦ f.map) (tensorDiagonal_projectionLeft P)

theorem tensorDiagonal_map_right (P : Code.{u}) :
    (tensorDiagonal P).map ≫ (tensorProjectionRight P P).map = 𝟙 P.space :=
  congrArg (fun f : P ⟶ P ↦ f.map) (tensorDiagonal_projectionRight P)

variable (a b c d)

/-- The supplied gadget diagonal gives the first natural transformation, over the same map. -/
def gadgetPhiThetaUnit : 𝟭 (GadgetsOver (X ⊗ Y) (a, c) (b, d)) ⟶
    gadgetPhi a b c d ⋙ theta where
  app P := ObjectProperty.homMk (CostructuredArrow.homMk
    (tensorDiagonal P.obj.left) (by
      change (tensorDiagonal P.obj.left).map ≫
        (theta.obj ((gadgetPhi a b c d).obj P)).obj.hom = P.obj.hom
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, theta_obj_fst]
        change (tensorDiagonal P.obj.left).map ≫
          ((tensorProjectionLeft P.obj.left P.obj.left).map ≫
            (P.obj.hom ≫ fst X Y)) = P.obj.hom ≫ fst X Y
        rw [← Category.assoc, tensorDiagonal_map_left, Category.id_comp]
      · rw [Category.assoc, theta_obj_snd]
        change (tensorDiagonal P.obj.left).map ≫
          ((tensorProjectionRight P.obj.left P.obj.left).map ≫
            (P.obj.hom ≫ snd X Y)) = P.obj.hom ≫ snd X Y
        rw [← Category.assoc, tensorDiagonal_map_right, Category.id_comp]))
  naturality {P Q} h := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    change h.hom.left ≫ tensorDiagonal Q.obj.left =
      tensorDiagonal P.obj.left ≫ tensorMap _ _ h.hom.left h.hom.left
    apply tensorHom_ext
    · simp only [Category.assoc, tensorDiagonal_projectionLeft, tensorMap_projectionLeft,
        Category.comp_id]
      rw [← Category.assoc, tensorDiagonal_projectionLeft, Category.id_comp]
    · simp only [Category.assoc, tensorDiagonal_projectionRight, tensorMap_projectionRight,
        Category.comp_id]
      rw [← Category.assoc, tensorDiagonal_projectionRight, Category.id_comp]

/-- Both original projections give the reverse natural transformation. -/
def gadgetThetaPhiCounit : theta ⋙ gadgetPhi a b c d ⟶
    𝟭 (GadgetsOver X a b × GadgetsOver Y c d) where
  app P :=
    (ObjectProperty.homMk (CostructuredArrow.homMk
      (tensorProjectionLeft P.1.obj.left P.2.obj.left) (theta_obj_fst P).symm),
     ObjectProperty.homMk (CostructuredArrow.homMk
      (tensorProjectionRight P.1.obj.left P.2.obj.left) (theta_obj_snd P).symm))
  naturality {P Q} h := by
    apply Prod.ext
    · apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      exact tensorMap_projectionLeft _ _ h.1.hom.left h.2.hom.left
    · apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      exact tensorMap_projectionRight _ _ h.1.hom.left h.2.hom.left

theorem gadgetPhiThetaUnit_app_map (P : GadgetsOver (X ⊗ Y) (a, c) (b, d)) :
    ((gadgetPhiThetaUnit a b c d).app P).hom.left.map =
      CartesianMonoidalCategory.lift (𝟙 P.obj.left.space) (𝟙 P.obj.left.space) ≫
        (tensorSpaceIso P.obj.left P.obj.left).inv := rfl

theorem gadgetThetaPhiCounit_app_left (P : GadgetsOver X a b × GadgetsOver Y c d) :
    ((gadgetThetaPhiCounit a b c d).app P).1.hom.left =
      tensorProjectionLeft P.1.obj.left P.2.obj.left := rfl

theorem gadgetThetaPhiCounit_app_right (P : GadgetsOver X a b × GadgetsOver Y c d) :
    ((gadgetThetaPhiCounit a b c d).app P).2.hom.left =
      tensorProjectionRight P.1.obj.left P.2.obj.left := rfl

end

end DaggerOriginalProductGadget
