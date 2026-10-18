import OriginalNecklaceCutFlags
import ChosenNecklaceWedgeFlags

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable (T : NecklaceCode) (j : Fin (T.len + 1))

/-- The original two cut inclusions extend across the actual necklace wedge. -/
def cutWedgeMap : (NecklaceCode.wedge (cutLeft T j) (cutRight T j)).toSSet ⟶ toSSet.{u} T :=
  wedgeDesc _ _ (cutLeftι T j) (cutRightι T j) (cut_comm T j)

theorem cutWedge_left :
    wedgeιLeft (cutLeft T j) (cutRight T j) ≫ cutWedgeMap.{u} T j = cutLeftι T j :=
  wedgeDesc_left _ _ _ _ _

theorem cutWedge_right :
    wedgeιRight (cutLeft T j) (cutRight T j) ≫ cutWedgeMap.{u} T j = cutRightι T j :=
  wedgeDesc_right _ _ _ _ _

/-- Both original outer endpoints are preserved, including cuts at the endpoints. -/
def cutWedgeHom : NecklaceCode.Hom.{u} (NecklaceCode.wedge (cutLeft T j) (cutRight T j)) T where
  map := cutWedgeMap T j
  first := by
    rw [← wedgeιLeft_first]
    change (wedgeιLeft (cutLeft T j) (cutRight T j) ≫ cutWedgeMap T j).app _
      (cutLeft T j).first = T.first
    rw [cutWedge_left]
    exact intervalι_first T 0 j (Fin.zero_le j)
  last := by
    rw [← wedgeιRight_last]
    change (wedgeιRight (cutLeft T j) (cutRight T j) ≫ cutWedgeMap T j).app _
      (cutRight T j).last = T.last
    rw [cutWedge_right]
    exact intervalι_last T j (Fin.last T.len) (Fin.le_last j)

/-- The cut flag inverse is exactly the original flag wedge followed by the code map. -/
theorem cutWedge_flag (hj : j ∈ T.joints) {n : ℕ}
    (F : Flag.{u} (cutLeft T j) n) (G : Flag.{u} (cutRight T j) n) :
    NecklaceCode.Flag.map (cutWedgeHom T j) (NecklaceCode.Flag.wedge F G) =
      (cutFlagIso T j hj).inv.app (op ⦋n⦌) (F, G) := by
  apply NecklaceCode.Flag.ext
  intro i
  apply Eq.trans ?_ (cutFlagIso_inv_chain T j hj F G i).symm
  have hl := congrArg mapVertices (cutWedge_left.{u} T j)
  have hr := congrArg mapVertices (cutWedge_right.{u} T j)
  rw [mapVertices_comp] at hl hr
  change mapVertices (cutWedgeMap T j) ''
      (mapVertices (wedgeιLeft (cutLeft T j) (cutRight T j)) '' F.chain i ∪
        mapVertices (wedgeιRight (cutLeft T j) (cutRight T j)) '' G.chain i) = _
  simp only [Set.image_union, Set.image_image]
  change (mapVertices (cutWedgeMap T j) ∘
      mapVertices (wedgeιLeft (cutLeft T j) (cutRight T j))) '' F.chain i ∪
    (mapVertices (cutWedgeMap T j) ∘
      mapVertices (wedgeιRight (cutLeft T j) (cutRight T j))) '' G.chain i = _
  rw [hl, hr]

theorem cutWedge_split_flag (hj : j ∈ T.joints) {n : ℕ} (F : Flag.{u} T n) :
    NecklaceCode.Flag.map (cutWedgeHom T j)
        (NecklaceCode.Flag.wedge (((cutFlagIso T j hj).hom.app (op ⦋n⦌) F).1)
          (((cutFlagIso T j hj).hom.app (op ⦋n⦌) F).2)) = F := by
  rw [cutWedge_flag T j hj]
  exact congrArg (fun f ↦ f.app (op ⦋n⦌) F) (cutFlagIso.{u} T j hj).hom_inv_id

end

end DaggerOriginalProductGadget
