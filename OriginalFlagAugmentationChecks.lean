import OriginalFlagAugmentationGeometric

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory

universe u

namespace DaggerOriginalFlagAugmentationChecks

noncomputable section

open DaggerOriginalFlagFlankification DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

theorem original_augmentation_geometric :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (nerveMap (augmentation X a b n)))) :=
  augmentation_geometric X a b n

theorem original_augmentation_R_maps :
    (augmentationHomotopyEquiv X a b n).hom = R.map (nerveMap (augmentation X a b n)) ∧
      (augmentationHomotopyEquiv X a b n).inv = R.map (nerveMap (centers X a b n)) :=
  ⟨augmentationHomotopyEquiv_hom X a b n, augmentationHomotopyEquiv_inv X a b n⟩

def original_augmentation_homInvId :
    SSet.Homotopy
      (R.map (nerveMap (augmentation X a b n)) ≫ R.map (nerveMap (centers X a b n)))
      (𝟙 (R.obj (nerve (Degree X a b n)))) :=
  augmentationHomInvId X a b n

def original_augmentation_invHomId :
    SSet.Homotopy
      (R.map (nerveMap (centers X a b n)) ≫ R.map (nerveMap (augmentation X a b n)))
      (𝟙 (R.obj (nerve (Discrete ((flagHom X a b).obj (op ⦋n⦌)))))) :=
  augmentationInvHomId X a b n

theorem original_center_class (t : (flagHom X a b).obj (op ⦋n⦌)) :
    classOf X a b n ((centers X a b n).obj (Discrete.mk t)) = t :=
  centerDegreeObj_class X a b n t

theorem original_center_iso_triangles :
    (centersAugmentationIso X a b n).hom ≫ (centersAugmentationIso X a b n).inv =
        𝟙 (centers X a b n ⋙ augmentation X a b n) ∧
      (centersAugmentationIso X a b n).inv ≫ (centersAugmentationIso X a b n).hom =
        𝟙 (𝟭 (Discrete ((flagHom X a b).obj (op ⦋n⦌)))) :=
  ⟨centersAugmentationIso_hom_inv X a b n, centersAugmentationIso_inv_hom X a b n⟩

theorem original_equal_class_transport
    {s t : Discrete ((flagHom X a b).obj (op ⦋n⦌))} (e : s ⟶ t) :
    (centers X a b n).map e =
      eqToHom (congrArg (centerDegreeObj X a b n) (Discrete.eq_of_hom e)) :=
  centers_map X a b n e

theorem original_beta_naturality {p q : Degree X a b n} (f : p ⟶ q) :
    (flankification X a b n).map f ≫ (toCenters X a b n).app q =
      (toCenters X a b n).app p ≫ (augmentation X a b n ⋙ centers X a b n).map f :=
  flankToCenterArrow_naturality X a b n f

theorem original_beta_flag (p : Degree X a b n) :
    NecklaceCode.Flag.map ((toCenters X a b n).app p).val.hom
        ((flankification X a b n).obj p).2 =
      (centerDegreeObj X a b n (classOf X a b n p)).2 :=
  toCenters_flag X a b n p

theorem original_beta_all_operators {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (gamma : (nerve (Degree X a b n)).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (nerve (Degree X a b n)).map e
        ((toCentersNerveHomotopy X a b n).h.app k (gamma, s)) =
      (toCentersNerveHomotopy X a b n).h.app l
        ((nerve (Degree X a b n)).map e gamma, (SSet.stdSimplex.obj ⦋1⦌).map e s) :=
  toCentersNerveHomotopy_simplex X a b n e gamma s

theorem original_empty_quotient
    (_hQ : IsEmpty ((flagHom X a b).obj (op ⦋n⦌))) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (nerveMap (augmentation X a b n)))) :=
  augmentation_geometric X a b n

theorem original_diagonal_zero (Y : SSet.{0}) (z : Y.obj (op ⦋0⦌)) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (nerveMap (augmentation Y z z 0)))) :=
  augmentation_geometric Y z z 0

end

end DaggerOriginalFlagAugmentationChecks
