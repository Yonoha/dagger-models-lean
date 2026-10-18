import OriginalGateSplitRetraction
import ChosenNecklaceIntervalTerminal

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable (T U : NecklaceCode)

/-- The actual shared joint of the original wedge, including either point factor. -/
def wedgeCutJoint : Fin ((NecklaceCode.wedge T U).len + 1) :=
  wedgeLeft T U (Fin.last T.len)

theorem wedgeCutJoint_mem : wedgeCutJoint T U ∈ (NecklaceCode.wedge T U).joints :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, T.last_mem, rfl⟩)

/-- The original left wedge leg, with the shared vertex as its specified last endpoint. -/
def wedgeLeftIntervalOver : NecklacesOver (NecklaceCode.wedge T U).toSSet
    (NecklaceCode.wedge T U).first
    ((NecklaceCode.wedge T U).verticesEquiv.symm (ULift.up (wedgeCutJoint T U))) where
  code := T
  map := wedgeιLeft T U
  first := wedgeιLeft_first T U
  last := by
    apply (NecklaceCode.wedge T U).verticesEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact wedgeιLeft_vertices T U (ULift.up (Fin.last T.len))

/-- The original right wedge leg, with the same shared vertex as its first endpoint. -/
def wedgeRightIntervalOver : NecklacesOver (NecklaceCode.wedge T U).toSSet
    ((NecklaceCode.wedge T U).verticesEquiv.symm (ULift.up (wedgeCutJoint T U)))
    (NecklaceCode.wedge T U).last where
  code := U
  map := wedgeιRight T U
  first := by
    apply (NecklaceCode.wedge T U).verticesEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (wedgeιRight_vertices T U (ULift.up 0)).trans
      (congrArg ULift.up (wedge_joint T U).symm)
  last := wedgeιRight_last T U

/-- Reuse the existing terminal interval factorization for the left wedge leg. -/
def wedgeLeftCutHom : NecklaceCode.Hom.{u} T
    (cutLeft (NecklaceCode.wedge T U) (wedgeCutJoint T U)) :=
  (toInterval _ 0 _ (Fin.zero_le _) (wedgeLeftIntervalOver T U)).hom

/-- Reuse the same terminal interval factorization for the right wedge leg. -/
def wedgeRightCutHom : NecklaceCode.Hom.{u} U
    (cutRight (NecklaceCode.wedge T U) (wedgeCutJoint T U)) :=
  (toInterval _ _ (Fin.last _) (Fin.le_last _) (wedgeRightIntervalOver T U)).hom

theorem wedgeLeftCutHom_fac :
    (wedgeLeftCutHom.{u} T U).map ≫
      cutLeftι (NecklaceCode.wedge T U) (wedgeCutJoint T U) = wedgeιLeft T U :=
  (toInterval _ 0 _ (Fin.zero_le _) (wedgeLeftIntervalOver T U)).w

theorem wedgeRightCutHom_fac :
    (wedgeRightCutHom.{u} T U).map ≫
      cutRightι (NecklaceCode.wedge T U) (wedgeCutJoint T U) = wedgeιRight T U :=
  (toInterval _ _ (Fin.last _) (Fin.le_last _) (wedgeRightIntervalOver T U)).w

/-- The original cut isomorphism sends a wedge flag to the two original flags
transported by the actual terminal interval arrows. -/
theorem cutFlagIso_wedge {d : ℕ} (F : Flag.{u} T d) (G : Flag.{u} U d) :
    (cutFlagIso (NecklaceCode.wedge T U) (wedgeCutJoint T U)
      (wedgeCutJoint_mem T U)).hom.app (op ⦋d⦌) (NecklaceCode.Flag.wedge F G) =
      (NecklaceCode.Flag.map (wedgeLeftCutHom T U) F,
        NecklaceCode.Flag.map (wedgeRightCutHom T U) G) := by
  let e := cutFlagIso.{u} (NecklaceCode.wedge T U) (wedgeCutJoint T U)
    (wedgeCutJoint_mem T U)
  apply injective_of_mono (e.inv.app (op ⦋d⦌))
  have h := congrFun (NatTrans.congr_app e.hom_inv_id (op ⦋d⦌))
    (NecklaceCode.Flag.wedge F G)
  change e.inv.app _ (e.hom.app _ (NecklaceCode.Flag.wedge F G)) = _ at h
  change e.inv.app _ (e.hom.app _ (NecklaceCode.Flag.wedge F G)) = _
  rw [h]
  symm
  apply NecklaceCode.Flag.ext
  intro i
  rw [cutFlagIso_inv_chain]
  change mapVertices (cutLeftι _ _) ''
      (mapVertices (wedgeLeftCutHom T U).map '' F.chain i) ∪
    mapVertices (cutRightι _ _) ''
      (mapVertices (wedgeRightCutHom T U).map '' G.chain i) = _
  rw [Set.image_image, Set.image_image]
  change (mapVertices (cutLeftι _ _) ∘ mapVertices (wedgeLeftCutHom T U).map) '' F.chain i ∪
    (mapVertices (cutRightι _ _) ∘ mapVertices (wedgeRightCutHom T U).map) '' G.chain i = _
  rw [← mapVertices_comp, ← mapVertices_comp, wedgeLeftCutHom_fac, wedgeRightCutHom_fac]
  rfl

end

end DaggerOriginalProductGadget
