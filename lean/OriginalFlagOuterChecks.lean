import OriginalFlagOuterDegree

set_option autoImplicit false
open CategoryTheory Opposite Simplicial

universe u
namespace DaggerOriginalFlagFlankification
noncomputable section
open DaggerChosenRigidificationNecklace

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

theorem check_rawPiZero_representative (n : ℕ) (p : Degree X a b n) :
    rawPiZeroEquiv X a b n (SSet.π₀.mk (ComposableArrows.mk₀ p)) =
      classOf X a b n p := rawPiZeroEquiv_mk X a b n p

theorem check_whole_outer_naturality {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    (outerNerve X a b).map α ≫ (outerEta X a b).app r =
      (outerEta X a b).app q ≫ (outerConstant X a b).map α :=
  (outerEta X a b).naturality α

theorem check_row_is_original (n : ℕ) :
    (outerEta X a b).app (op ⦋n⦌) = constantAugmentation X a b n :=
  outerEta_app_degree X a b n

theorem check_diagonal_representative (n : ℕ)
    (gamma : ((outerNerve X a b).obj (op ⦋n⦌)).obj (op ⦋n⦌)) :
    (diagonalAugmentation X a b).app (op ⦋n⦌) gamma =
      classOf X a b n (gamma.obj 0) :=
  diagonalAugmentation_representative X a b n gamma

end
end DaggerOriginalFlagFlankification
