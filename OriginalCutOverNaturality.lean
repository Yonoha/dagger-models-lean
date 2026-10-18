import OriginalCutFlagNaturality
import OriginalProductCrossingFlag

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {P Q : NecklacesOver X a b}
  (g : NecklacesOver.Hom P Q) (k : Fin (P.code.len + 1)) (l : Fin (Q.code.len + 1))
  (h : orderMap g.hom.map k = l)

include g h in
/-- The original over-X equation identifies the actual two cut middle vertices. -/
theorem cutMiddleVertex_naturality : cutMiddleVertex P k = cutMiddleVertex Q l := by
  calc
    P.map.app _ (P.code.verticesEquiv.symm (ULift.up k)) =
        Q.map.app _ (g.hom.map.app _ (P.code.verticesEquiv.symm (ULift.up k))) :=
      (congrFun (NatTrans.congr_app g.w _) _).symm
    _ = _ := congrArg (Q.map.app _) (necklaceMap_vertex_of_order g.hom.map k l h)

theorem cutLeftOver_naturality :
    (cutLeftHom g.hom k l h).map ≫ (cutLeftOver Q l).map = (cutLeftOver P k).map := by
  change (cutLeftHom g.hom k l h).map ≫ (cutLeftι Q.code l ≫ Q.map) =
    cutLeftι P.code k ≫ P.map
  rw [← Category.assoc, cutLeftHom_fac, Category.assoc, g.w]

theorem cutRightOver_naturality :
    (cutRightHom g.hom k l h).map ≫ (cutRightOver Q l).map = (cutRightOver P k).map := by
  change (cutRightHom g.hom k l h).map ≫ (cutRightι Q.code l ≫ Q.map) =
    cutRightι P.code k ≫ P.map
  rw [← Category.assoc, cutRightHom_fac, Category.assoc, g.w]

/-- At matched actual joints, every original over-X arrow respects both cut flags. -/
theorem cutFlagOver_map (hk : k ∈ P.code.joints) (hl : l ∈ Q.code.joints)
    {n : ℕ} (F : Flag.{u} P.code n) :
    (cutFlagIso Q.code l hl).hom.app (op ⦋n⦌) (NecklaceCode.Flag.map g.hom F) =
      (NecklaceCode.Flag.map (cutLeftHom g.hom k l h)
          (((cutFlagIso P.code k hk).hom.app (op ⦋n⦌) F).1),
        NecklaceCode.Flag.map (cutRightHom g.hom k l h)
          (((cutFlagIso P.code k hk).hom.app (op ⦋n⦌) F).2)) :=
  congrArg (fun f ↦ f.app (op ⦋n⦌) F) (cutFlagIso_naturality g.hom k l h hk hl)

/-- Every specified target cut lifts to an actual source joint along any original over-X arrow. -/
theorem cutOver_joint_lift (hl : l ∈ Q.code.joints) :
    ∃ k ∈ P.code.joints, orderMap g.hom.map k = l :=
  Finset.mem_image.mp (joints_subset_image g.hom hl)

/-- A lifted source cut still maps to the same joint in the original necklace factor. -/
theorem productCutOver_joint_lift (K : SSet.{u}) (T : NecklaceCode)
    {a b : (K ⨯ T.toSSet).obj (op ⦋0⦌)}
    {P Q : NecklacesOver (K ⨯ T.toSSet) a b} (g : NecklacesOver.Hom P Q)
    (l : Fin (Q.code.len + 1)) (hl : l ∈ Q.code.joints)
    (j : Fin (T.len + 1)) (hj : orderMap (Q.map ≫ prod.snd) l = j) :
    ∃ k ∈ P.code.joints, orderMap g.hom.map k = l ∧
      orderMap (P.map ≫ prod.snd) k = j := by
  obtain ⟨k, hk, he⟩ := cutOver_joint_lift g l hl
  refine ⟨k, hk, he, ?_⟩
  rw [← g.w, Category.assoc, orderMap_comp_apply, he, hj]

end

end DaggerOriginalProductGadget
