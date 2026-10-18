import OriginalFlagConstantAugmentation

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification.ConstantTargetChecks

noncomputable section

open DaggerOriginalFlagFlankification DaggerChosenRigidificationNecklace

def supplied_constant_target (Q : Type u) : nerve (Discrete Q) ≅ constantSSet Q :=
  nerveDiscreteIso Q

theorem full_inverse_pair (Q : Type u) :
    (nerveDiscreteIso Q).hom ≫ (nerveDiscreteIso Q).inv = 𝟙 (nerve (Discrete Q)) ∧
      (nerveDiscreteIso Q).inv ≫ (nerveDiscreteIso Q).hom = 𝟙 (constantSSet Q) :=
  ⟨nerveDiscreteIso_hom_inv Q, nerveDiscreteIso_inv_hom Q⟩

theorem supplied_inverse_chain_object (Q : Type u) (k : SimplexCategoryᵒᵖ) (t : Q)
    (i : Fin (k.unop.len + 1)) :
    ((nerveDiscreteIso Q).inv.app k t).obj i = Discrete.mk t := rfl

theorem arbitrary_operator_value (Q : Type u) {k l : SimplexCategoryᵒᵖ}
    (alpha : k ⟶ l) (gamma : (nerve (Discrete Q)).obj k) :
    (nerveDiscreteIso Q).hom.app l ((nerve (Discrete Q)).map alpha gamma) =
      (gamma.obj (alpha.unop.toOrderHom 0)).as :=
  nerveDiscreteIso_hom_operator Q alpha gamma

/-- The first face really evaluates at object1, rather than assuming alpha(0)=0. -/
theorem first_face_is_nonzero (Q : Type u)
    (gamma : (nerve (Discrete Q)).obj (op ⦋1⦌)) :
    (nerveDiscreteIso Q).hom.app (op ⦋0⦌)
        ((nerve (Discrete Q)).map (SimplexCategory.δ (0 : Fin 2)).op gamma) =
      (gamma.obj 1).as := rfl

def empty_type_iso :
    nerve (Discrete PEmpty.{u+1}) ≅ constantSSet PEmpty.{u+1} :=
  nerveDiscreteIso PEmpty.{u+1}

def universe_zero_iso (Q : Type 0) : nerve (Discrete Q) ≅ constantSSet Q :=
  nerveDiscreteIso Q

theorem original_row_class (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (k : SimplexCategoryᵒᵖ) (gamma : (nerve (Degree X a b n)).obj k) :
    (constantAugmentation X a b n).app k gamma = classOf X a b n (gamma.obj 0) :=
  constantAugmentation_app X a b n k gamma

theorem diagonal_zero_row (X : SSet.{u}) (a : X.obj (op ⦋0⦌))
    (gamma : (nerve (Degree X a a 0)).obj (op ⦋0⦌)) :
    (constantAugmentation X a a 0).app (op ⦋0⦌) gamma =
      classOf X a a 0 (gamma.obj 0) := rfl

theorem original_row_geometric (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (constantAugmentation X a b n))) :=
  constantAugmentation_geometric X a b n

end

end DaggerOriginalFlagFlankification.ConstantTargetChecks
