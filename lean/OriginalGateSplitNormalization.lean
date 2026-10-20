import OriginalSpecifiedGateSplit

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a v b : X.obj (op ⦋0⦌)}

/-- The image of a specified original joint is still an actual joint after normalization. -/
theorem normalizedGateJoint_mem (P : NecklacesOver X a b) (k : Fin (P.code.len + 1))
    (hk : k ∈ P.code.joints) :
    orderMap (originalNormalization P).hom.map k ∈ (normOver P).code.joints := by
  have h : mapVertices (originalNormalization P).hom.map (ULift.up k) ∈
      mapVertices (originalNormalization P).hom.map '' {z | z.down ∈ P.code.joints} :=
    ⟨ULift.up k, hk, rfl⟩
  rw [originalNormalization_joint_image] at h
  exact h

variable (hm : ∀ P : NecklacesOver X a b,
  (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)

/-- Normalize the original necklace while retaining the specified actual target gate. -/
def normalizedGate (P : NecklacesOver X a b) (k : Fin (P.code.len + 1))
    (hk : k ∈ P.code.joints) (hv : cutMiddleVertex P k = v) :
    MonicGateNecklaces a b {v} :=
  ⟨normOver P, hm _ (normOver_beads_nondegenerate P),
    Set.singleton_subset_iff.mpr ⟨_, normalizedGateJoint_mem P k hk,
      (vertexImage_over_map (originalNormalization P) k).trans hv⟩⟩

/-- The normalized gate's unique chosen joint is the image of the specified source joint. -/
theorem normalizedGate_joint (P : NecklacesOver X a b) (k : Fin (P.code.len + 1))
    (hk : k ∈ P.code.joints) (hv : cutMiddleVertex P k = v) :
    orderMap (originalNormalization P).hom.map k = gateJoint (normalizedGate hm P k hk hv) :=
  gateJoint_unique (normalizedGate hm P k hk hv) (orderMap (originalNormalization P).hom.map k)
    ((vertexImage_over_map (originalNormalization P) k).trans hv)

/-- The actual split agrees with colimit descent on the original canonical comparison. -/
theorem monicGateComparison_split :
    monicGateComparison a b {v} ≫ gateSubcomplexSplit a v b hm = gateSplit a v b := by
  change (monicGateIso {v} hm).hom ≫ ((monicGateIso {v} hm).inv ≫ gateSplit a v b) = _
  rw [Iso.hom_inv_id_assoc]

/-- Evaluate the actual split on an original monomorphic gate representative. -/
theorem gateSubcomplexSplit_monic {d : ℕ} (P : MonicGateNecklaces a b {v})
    (F : Flag.{u} P.obj.code d) :
    (gateSubcomplexSplit a v b hm).app (op ⦋d⦌)
      ((monicGateComparison a b {v}).app (op ⦋d⦌) (Quot.mk _ ⟨P, F⟩)) =
        (gateSplitLeg P).app (op ⦋d⦌) F :=
  congrFun (NatTrans.congr_app (monicGateComparison_split hm) (op ⦋d⦌)) (Quot.mk _ ⟨P, F⟩)

/-- The actual split may be computed using any original representative and any supplied
joint above the gate: normalization and all original cut arrows prove this formula. -/
theorem gateSubcomplexSplit_original {d : ℕ} (P : NecklacesOver X a b)
    (k : Fin (P.code.len + 1)) (hk : k ∈ P.code.joints)
    (hv : cutMiddleVertex P k = v) (F : Flag.{u} P.code d)
    (x : (flagGateSubcomplex a b {v}).obj (op ⦋d⦌))
    (hx : x.val = Quot.mk (flagRelation X a b (op ⦋d⦌)) ⟨P, F⟩) :
    (gateSubcomplexSplit a v b hm).app (op ⦋d⦌) x =
      (specifiedSplit P k hk hv).app (op ⦋d⦌) F := by
  let N := normalizedGate hm P k hk hv
  have he : x = (monicGateComparison a b {v}).app (op ⦋d⦌)
      (Quot.mk _ ⟨N, originalNormalizedFlag P F⟩) := by
    apply Subtype.ext
    exact hx.trans (Quot.sound ⟨originalNormalization P, rfl⟩)
  rw [he, gateSubcomplexSplit_monic]
  have hn := specifiedSplit_naturality (originalNormalization P) k (gateJoint N)
    (normalizedGate_joint hm P k hk hv) hv (gateJoint_middle N) hk (gateJoint_mem N)
  exact congrFun (NatTrans.congr_app hn (op ⦋d⦌)) F

end

end DaggerOriginalProductGadget
