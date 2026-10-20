import OriginalFlagAugmentationChecks

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerOriginalFlagFlankification DaggerNerveHomotopy

universe u

noncomputable section

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ),
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (nerveMap (augmentation X a b n)))) :=
  augmentation_geometric

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ),
    (augmentationHomotopyEquiv X a b n).hom = R.map (nerveMap (augmentation X a b n)) ∧
      (augmentationHomotopyEquiv X a b n).inv = R.map (nerveMap (centers X a b n)) :=
  DaggerOriginalFlagAugmentationChecks.original_augmentation_R_maps

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ),
    SSet.Homotopy
      (R.map (nerveMap (augmentation X a b n)) ≫ R.map (nerveMap (centers X a b n)))
      (𝟙 (R.obj (nerve (Degree X a b n)))) :=
  augmentationHomInvId

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ),
    SSet.Homotopy
      (R.map (nerveMap (centers X a b n)) ≫ R.map (nerveMap (augmentation X a b n)))
      (𝟙 (R.obj (nerve (Discrete ((DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌)))))) :=
  augmentationInvHomId

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌)),
    classOf X a b n ((centers X a b n).obj (Discrete.mk t)) = t :=
  DaggerOriginalFlagAugmentationChecks.original_center_class

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p q : Degree X a b n) (f : p ⟶ q),
    (flankification X a b n).map f ≫ (toCenters X a b n).app q =
      (toCenters X a b n).app p ≫ (augmentation X a b n ⋙ centers X a b n).map f :=
  fun X a b n _ _ f ↦ flankToCenterArrow_naturality X a b n f

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ),
    SSet.ι₀ ≫ (toCentersNerveHomotopy X a b n).h = nerveMap (flankification X a b n) ∧
      SSet.ι₁ ≫ (toCentersNerveHomotopy X a b n).h =
        nerveMap (augmentation X a b n ⋙ centers X a b n) :=
  fun X a b n ↦ ⟨toCentersNerveHomotopy_zero X a b n, toCentersNerveHomotopy_one X a b n⟩

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (k l : SimplexCategoryᵒᵖ) (e : k ⟶ l)
    (gamma : (nerve (Degree X a b n)).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k),
    (nerve (Degree X a b n)).map e
        ((toCentersNerveHomotopy X a b n).h.app k (gamma, s)) =
      (toCentersNerveHomotopy X a b n).h.app l
        ((nerve (Degree X a b n)).map e gamma, (SSet.stdSimplex.obj ⦋1⦌).map e s) :=
  fun X a b n _ _ e gamma s ↦ toCentersNerveHomotopy_simplex X a b n e gamma s

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (_hQ : IsEmpty ((DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌))),
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (nerveMap (augmentation X a b n)))) :=
  fun X a b n _ ↦ augmentation_geometric X a b n

example : ∀ (X : SSet.{0}) (a : X.obj (op ⦋0⦌)),
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (nerveMap (augmentation X a a 0)))) :=
  fun X a ↦ augmentation_geometric X a a 0

end
