import NativeSimplicialReplacement
import ProofActualConeIndexWeakness

/-! Reuse the entire original flag bidegree equivalence as a simplicial-replacement isomorphism. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualNecklaceFlagReplacement
noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

/-- Each entire original bidegree is the original necklace chain and its first whole flag. -/
def replacementIso : originalB X a b ≅ replacement (NecklacesOver.flagDiagram X a b) :=
  NatIso.ofComponents (fun q ↦ NatIso.ofComponents
    (fun k ↦ (bidegreeEquiv X a b q k).toIso) (by
      intro k l β
      funext γ
      change bidegreeToRaw X a b q l (((originalB X a b).obj q).map β γ) = _
      rw [bidegreeToRaw_inner]
      rfl)) (by
    intro q r α
    apply NatTrans.ext
    funext k γ
    change bidegreeToRaw X a b r k (((originalB X a b).map α).app k γ) = _
    apply Sigma.ext (bidegreeToRaw_outer_chain X a b α k γ)
    exact heq_of_eq (bidegreeToRaw_outer_flag X a b α k γ))

/-- The full diagonal isomorphism retains every original chain and all simplex operators. -/
def diagonalIso : DaggerBisimplicialDiagonal.diag (originalB X a b) ≅
    DaggerBisimplicialDiagonal.diag (replacement (NecklacesOver.flagDiagram X a b)) :=
  (DaggerBisimplicialDiagonal.diagonalFunctor).mapIso (replacementIso X a b)

/-- The actual original Pi is exactly the whole-chain projection of this replacement. -/
theorem projection_original : (diagonalIso X a b).hom ≫
    diagonalProjection (NecklacesOver.flagDiagram X a b) = originalPi X a b := by
  apply NatTrans.ext
  rfl

end
end DaggerActualNecklaceFlagReplacement
