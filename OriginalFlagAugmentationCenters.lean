import OriginalFlagFiberTerminal
import Mathlib.CategoryTheory.Discrete.Basic

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

/-- The same center, retaining its original degree object and complete flag. -/
def centerDegreeObj (t : (flagHom X a b).obj (op ⦋n⦌)) : Degree X a b n :=
  (fiberCenter X a b n t).obj.obj

def centerFlankedDegreeObj (t : (flagHom X a b).obj (op ⦋n⦌)) :
    FlankedDegree X a b n :=
  ⟨centerDegreeObj X a b n t, (fiberCenter X a b n t).property⟩

theorem centerDegreeObj_class (t : (flagHom X a b).obj (op ⦋n⦌)) :
    classOf X a b n (centerDegreeObj X a b n t) = t :=
  fiberCenter_class X a b n t

theorem centerDegreeObj_nondegenerate (t : (flagHom X a b).obj (op ⦋n⦌)) :
    TotallyNondegenerate X a b n (centerDegreeObj X a b n t) :=
  fiberCenter_nondegenerate X a b n t

/-- Empty quotient types need no globally chosen representative. -/
def centers : Discrete ((flagHom X a b).obj (op ⦋n⦌)) ⥤ Degree X a b n :=
  Discrete.functor (centerDegreeObj X a b n)

theorem centers_obj (t : (flagHom X a b).obj (op ⦋n⦌)) :
    (centers X a b n).obj (Discrete.mk t) = centerDegreeObj X a b n t := rfl

/-- Equal-class arrows keep the actual dependent center transport. -/
theorem centers_map {s t : Discrete ((flagHom X a b).obj (op ⦋n⦌))} (e : s ⟶ t) :
    (centers X a b n).map e =
      eqToHom (congrArg (centerDegreeObj X a b n) (Discrete.eq_of_hom e)) := rfl

def centersAugmentationIso :
    centers X a b n ⋙ augmentation X a b n ≅
      𝟭 (Discrete ((flagHom X a b).obj (op ⦋n⦌))) :=
  Discrete.natIso (fun t ↦ Discrete.eqToIso (centerDegreeObj_class X a b n t.as))

theorem centersAugmentationIso_hom_app
    (t : Discrete ((flagHom X a b).obj (op ⦋n⦌))) :
    (centersAugmentationIso X a b n).hom.app t =
      Discrete.eqToHom (centerDegreeObj_class X a b n t.as) := rfl

theorem centersAugmentationIso_inv_app
    (t : Discrete ((flagHom X a b).obj (op ⦋n⦌))) :
    (centersAugmentationIso X a b n).inv.app t =
      Discrete.eqToHom (centerDegreeObj_class X a b n t.as).symm := rfl

theorem centersAugmentationIso_hom_inv :
    (centersAugmentationIso X a b n).hom ≫ (centersAugmentationIso X a b n).inv =
      𝟙 (centers X a b n ⋙ augmentation X a b n) :=
  (centersAugmentationIso X a b n).hom_inv_id

theorem centersAugmentationIso_inv_hom :
    (centersAugmentationIso X a b n).inv ≫ (centersAugmentationIso X a b n).hom =
      𝟙 (𝟭 (Discrete ((flagHom X a b).obj (op ⦋n⦌)))) :=
  (centersAugmentationIso X a b n).inv_hom_id

/-- The original categorical component map is exactly the original quotient bijection. -/
theorem augmentation_componentMap :
    ConnectedComponents.liftFunctor (Degree X a b n) (augmentation X a b n) =
      (componentEquiv X a b n).toFun := rfl

end

end DaggerOriginalFlagFlankification
