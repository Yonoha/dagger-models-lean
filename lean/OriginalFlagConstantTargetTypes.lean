import OriginalFlagConstantAugmentation

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace

example : ∀ (Q : Type u), nerve (Discrete Q) ≅ constantSSet Q :=
  fun Q ↦ nerveDiscreteIso Q

example : ∀ (Q : Type u),
    (nerveDiscreteIso Q).hom ≫ (nerveDiscreteIso Q).inv = 𝟙 (nerve (Discrete Q)) ∧
      (nerveDiscreteIso Q).inv ≫ (nerveDiscreteIso Q).hom = 𝟙 (constantSSet Q) :=
  fun Q ↦ ⟨nerveDiscreteIso_hom_inv Q, nerveDiscreteIso_inv_hom Q⟩

example : ∀ (Q : Type u) (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve (Discrete Q)).obj k),
    (nerveDiscreteIso Q).hom.app k gamma = (gamma.obj 0).as :=
  fun Q k gamma ↦ nerveDiscreteIso_hom_app Q k gamma

example : ∀ (Q : Type u) (k : SimplexCategoryᵒᵖ) (t : Q),
    (nerveDiscreteIso Q).inv.app k t = discreteConstantChain Q k t :=
  fun Q k t ↦ nerveDiscreteIso_inv_app Q k t

example : ∀ (Q : Type u) (k l : SimplexCategoryᵒᵖ) (alpha : k ⟶ l)
    (gamma : (nerve (Discrete Q)).obj k),
    (nerveDiscreteIso Q).hom.app l ((nerve (Discrete Q)).map alpha gamma) =
      (gamma.obj (alpha.unop.toOrderHom 0)).as :=
  fun Q k l alpha gamma ↦ nerveDiscreteIso_hom_operator Q (k := k) (l := l) alpha gamma

example : ∀ (Q : Type u) (k l : SimplexCategoryᵒᵖ) (alpha : k ⟶ l) (t : Q),
    (nerve (Discrete Q)).map alpha ((nerveDiscreteIso Q).inv.app k t) =
      (nerveDiscreteIso Q).inv.app l t :=
  fun Q k l alpha t ↦ nerveDiscreteIso_inv_naturality Q (k := k) (l := l) alpha t

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ),
    constantAugmentation X a b n = nerveMap (augmentation X a b n) ≫
      (nerveDiscreteIso ((DaggerChosenRigidificationNecklace.flagHom X a b).obj
        (op ⦋n⦌))).hom :=
  fun X a b n ↦ constantAugmentation_factor X a b n

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (k : SimplexCategoryᵒᵖ) (gamma : (nerve (Degree X a b n)).obj k),
    (constantAugmentation X a b n).app k gamma = classOf X a b n (gamma.obj 0) :=
  fun X a b n k gamma ↦ constantAugmentation_app X a b n k gamma

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (k l : SimplexCategoryᵒᵖ) (alpha : k ⟶ l)
    (gamma : (nerve (Degree X a b n)).obj k),
    (constantAugmentation X a b n).app l ((nerve (Degree X a b n)).map alpha gamma) =
      classOf X a b n (gamma.obj (alpha.unop.toOrderHom 0)) :=
  fun X a b n k l alpha gamma ↦ constantAugmentation_operator X a b n (k := k) (l := l) alpha gamma

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ),
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (constantAugmentation X a b n))) :=
  fun X a b n ↦ constantAugmentation_geometric X a b n

end

end DaggerOriginalFlagFlankification
