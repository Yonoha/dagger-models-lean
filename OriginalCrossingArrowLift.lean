import OriginalCutOverNaturality
import OriginalCutMapLaws

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- An arbitrary original over-product arrow lifts any specified target crossing cut.
The lifted source joint has the same interface coordinate and middle vertex,
both actual cut-map squares commute, and the whole original flag splitting is natural. -/
theorem productCrossingArrow_lift (K : SSet.{u}) (T : NecklaceCode)
    {a b : (K ⨯ T.toSSet).obj (op ⦋0⦌)}
    {P Q : NecklacesOver (K ⨯ T.toSSet) a b} (g : NecklacesOver.Hom P Q)
    (l : Fin (Q.code.len + 1)) (hl : l ∈ Q.code.joints)
    (j : Fin (T.len + 1)) (hj : orderMap (Q.map ≫ prod.snd) l = j) :
    ∃ (k : Fin (P.code.len + 1)) (hk : k ∈ P.code.joints)
      (he : orderMap g.hom.map k = l),
      orderMap (P.map ≫ prod.snd) k = j ∧
      cutMiddleVertex P k = cutMiddleVertex Q l ∧
      (cutLeftHom g.hom k l he).map ≫ (cutLeftOver Q l).map = (cutLeftOver P k).map ∧
      (cutRightHom g.hom k l he).map ≫ (cutRightOver Q l).map = (cutRightOver P k).map ∧
      flagMap g.hom ≫ (cutFlagIso Q.code l hl).hom =
        (cutFlagIso P.code k hk).hom ≫
          (flagMap (cutLeftHom g.hom k l he) ⊗ₘ flagMap (cutRightHom g.hom k l he)) := by
  obtain ⟨k, hk, he, hc⟩ := productCutOver_joint_lift K T g l hl j hj
  exact ⟨k, hk, he, hc, cutMiddleVertex_naturality g k l he,
    cutLeftOver_naturality g k l he, cutRightOver_naturality g k l he,
    cutFlagIso_naturality g.hom k l he hk hl⟩

end

end DaggerOriginalProductGadget
