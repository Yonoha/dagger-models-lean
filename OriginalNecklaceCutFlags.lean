import OriginalProductCrossingEndpoints
import ChosenNecklaceFlagEvaluationIso
import ChosenNecklacePathSplitting

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerChosenRigidificationNecklace.NecklaceThickening

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable (T : NecklaceCode) (j : Fin (T.len + 1)) (hj : j ∈ T.joints)

/-- Cutting at an actual joint decomposes the original flag simplicial set. -/
def cutFlagIso : flagSSet.{u} T ≅ flagSSet (cutLeft T j) ⊗ flagSSet (cutRight T j) :=
  outerFlagIso T ≪≫
    jointSplitIso j hj (Fin.zero_le j) (Fin.le_last j) ≪≫
      tensorIso (intervalOuterHomIso T 0 j (Fin.zero_le j)).symm
        (intervalOuterHomIso T j (Fin.last T.len) (Fin.le_last j)).symm

/-- The inverse is the literal union of the images under the two cut inclusions. -/
theorem cutFlagIso_inv_chain {n : ℕ}
    (F : Flag.{u} (cutLeft T j) n) (G : Flag.{u} (cutRight T j) n)
    (i : Fin (n + 1)) :
    (((cutFlagIso T j hj).inv.app (op ⦋n⦌) (F, G)).chain i) =
      mapVertices (cutLeftι T j) '' F.chain i ∪
        mapVertices (cutRightι T j) '' G.chain i := by
  change (((intervalOuterHomIso T 0 j (Fin.zero_le j)).hom.app (op ⦋n⦌) F).obj i).I ∪
    (((intervalOuterHomIso T j (Fin.last T.len) (Fin.le_last j)).hom.app
      (op ⦋n⦌) G).obj i).I = _
  rw [intervalOuterHomIso_I, intervalOuterHomIso_I]
  have hl : mapVertices (cutLeftι.{u} T j) = intervalOrderMap T 0 j (Fin.zero_le j) :=
    funext (intervalι_vertices T 0 j (Fin.zero_le j))
  have hr : mapVertices (cutRightι.{u} T j) =
      intervalOrderMap T j (Fin.last T.len) (Fin.le_last j) :=
    funext (intervalι_vertices T j (Fin.last T.len) (Fin.le_last j))
  rw [hl, hr]

/-- Splitting and taking the same union recovers every level of the supplied flag. -/
theorem cutFlagIso_recombine {n : ℕ} (F : Flag.{u} T n) (i : Fin (n + 1)) :
    mapVertices (cutLeftι T j) ''
        (((cutFlagIso T j hj).hom.app (op ⦋n⦌) F).1.chain i) ∪
      mapVertices (cutRightι T j) ''
        (((cutFlagIso T j hj).hom.app (op ⦋n⦌) F).2.chain i) = F.chain i := by
  rw [← cutFlagIso_inv_chain T j hj]
  have h := congrArg (fun f ↦ f.app (op ⦋n⦌) F) (cutFlagIso.{u} T j hj).hom_inv_id
  exact congrArg (fun H : Flag T n ↦ H.chain i) h

end

end DaggerOriginalProductGadget
