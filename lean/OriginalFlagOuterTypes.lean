import OriginalFlagOuterChecks

set_option autoImplicit false
open CategoryTheory Opposite Simplicial

universe u
namespace DaggerOriginalFlagFlankification
noncomputable section
open DaggerChosenRigidificationNecklace

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

example (n : ℕ) : SSet.π₀ (nerve (Degree X a b n)) ≃
    (flagHom X a b).obj (op ⦋n⦌) := rawPiZeroEquiv X a b n

example : outerNerve X a b ⟶ outerConstant X a b := outerEta X a b

example : DaggerBisimplicialDiagonal.diag (outerNerve X a b) ⟶
    flagHom X a b := diagonalAugmentation X a b

end
end DaggerOriginalFlagFlankification
