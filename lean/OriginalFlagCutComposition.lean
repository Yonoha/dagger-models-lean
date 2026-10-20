import OriginalNecklaceCutWedge
import ChosenFlagHomComposition

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
  (P : NecklacesOver X a b) (j : Fin (P.code.len + 1))

/-- The supplied map evaluated at the specified source joint. -/
def cutMiddleVertex : X.obj (op ⦋0⦌) :=
  P.map.app _ (P.code.verticesEquiv.symm (ULift.up j))

def cutLeftOver : NecklacesOver X a (cutMiddleVertex P j) where
  code := cutLeft P.code j
  map := cutLeftι P.code j ≫ P.map
  first := by
    change P.map.app _ ((intervalι P.code 0 j (Fin.zero_le j)).app _ _) = a
    rw [intervalι_first]
    exact P.first
  last := by
    change P.map.app _ ((intervalι P.code 0 j (Fin.zero_le j)).app _ _) = _
    rw [intervalι_last]
    rfl

def cutRightOver : NecklacesOver X (cutMiddleVertex P j) b where
  code := cutRight P.code j
  map := cutRightι P.code j ≫ P.map
  first := by
    change P.map.app _ ((intervalι P.code j (Fin.last P.code.len) (Fin.le_last j)).app _ _) = _
    rw [intervalι_first]
    rfl
  last := by
    change P.map.app _ ((intervalι P.code j (Fin.last P.code.len) (Fin.le_last j)).app _ _) = b
    rw [intervalι_last]
    exact P.last

/-- The cut-and-wedge necklace has a literal endpoint-preserving arrow over the original X. -/
def cutWedgeOver : NecklacesOver.Hom
    (NecklacesOver.wedge (cutLeftOver P j) (cutRightOver P j)) P where
  hom := cutWedgeHom P.code j
  w := by
    apply (wedgeIsPushout (cutLeft P.code j) (cutRight P.code j)).hom_ext
    · change wedgeιLeft _ _ ≫ cutWedgeMap P.code j ≫ P.map = _
      rw [← Category.assoc, cutWedge_left]
      exact (NecklacesOver.wedge_left (cutLeftOver P j) (cutRightOver P j)).symm
    · change wedgeιRight _ _ ≫ cutWedgeMap P.code j ≫ P.map = _
      rw [← Category.assoc, cutWedge_right]
      exact (NecklacesOver.wedge_right (cutLeftOver P j) (cutRightOver P j)).symm

/-- Every original flag representative is the original composition of its two cut flags. -/
theorem flagComp_cut (hj : j ∈ P.code.joints) {n : ℕ} (F : Flag.{u} P.code n) :
    flagCompApp
        (Quot.mk _ (⟨cutLeftOver P j,
          ((cutFlagIso P.code j hj).hom.app (op ⦋n⦌) F).1⟩ : RawFlag X a _ (op ⦋n⦌)))
        (Quot.mk _ (⟨cutRightOver P j,
          ((cutFlagIso P.code j hj).hom.app (op ⦋n⦌) F).2⟩ : RawFlag X _ b (op ⦋n⦌))) =
      Quot.mk _ (⟨P, F⟩ : RawFlag X a b (op ⦋n⦌)) := by
  exact Quot.sound ⟨cutWedgeOver P j, (cutWedge_split_flag P.code j hj F).symm⟩

end

end DaggerOriginalProductGadget
