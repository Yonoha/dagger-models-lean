import OriginalGateSplitNormalization

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} (a v b : X.obj (op ⦋0⦌))
variable (hm : ∀ P : NecklacesOver X a b,
  (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)

/-- Original composition followed by the established split preserves both original Hom factors. -/
theorem gateComposition_split :
    gateComposition a v b ≫ gateSubcomplexSplit a v b hm =
      𝟙 (flagHom X a v ⊗ flagHom X v b) := by
  apply NatTrans.ext
  funext q z
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d
  rcases z with ⟨x, y⟩
  induction x using Quot.ind with | _ p
  induction y using Quot.ind with | _ r
  exact (gateSubcomplexSplit_original hm (NecklacesOver.wedge p.1 r.1)
    (wedgeCutJoint p.1.code r.1.code) (wedgeCutJoint_mem p.1.code r.1.code)
    (wedgeCut_middle p.1 r.1) (NecklaceCode.Flag.wedge p.2 r.2)
    ((gateComposition a v b).app (op ⦋d⦌) (Quot.mk _ p, Quot.mk _ r)) rfl).trans
      (specifiedSplit_wedge p.1 r.1 p.2 r.2)

/-- The literal singleton-gate subcomplex is the product of the two original Hom spaces.
The inverse is the original composition, and both roundtrips are proved. -/
def gateHomProductIso :
    (flagGateSubcomplex a b {v}).toFunctor ≅ flagHom X a v ⊗ flagHom X v b where
  hom := gateSubcomplexSplit a v b hm
  inv := gateComposition a v b
  hom_inv_id := gateSubcomplexSplit_recompose a v b hm
  inv_hom_id := gateComposition_split a v b hm

/-- Under the comparison, the original inclusion is exactly original Hom composition. -/
theorem gateHomProductIso_inv_ι :
    (gateHomProductIso a v b hm).inv ≫ (flagGateSubcomplex a b {v}).ι =
      flagComposition X a v b := rfl

/-- The isomorphism computes the original two cut Hom classes for every supplied representative. -/
theorem gateHomProductIso_original {d : ℕ} (P : NecklacesOver X a b)
    (k : Fin (P.code.len + 1)) (hk : k ∈ P.code.joints)
    (hv : cutMiddleVertex P k = v) (F : Flag.{u} P.code d)
    (x : (flagGateSubcomplex a b {v}).obj (op ⦋d⦌))
    (hx : x.val = Quot.mk (flagRelation X a b (op ⦋d⦌)) ⟨P, F⟩) :
    (gateHomProductIso a v b hm).hom.app (op ⦋d⦌) x =
      (specifiedSplit P k hk hv).app (op ⦋d⦌) F :=
  gateSubcomplexSplit_original hm P k hk hv F x hx

/-- In the actual binary necklace product, the ordered-target premise is discharged. -/
def productCutGateHomIso (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a v b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)) :
    (flagGateSubcomplex a b {v}).toFunctor ≅
      flagHom (productSpace n factor ⨯ T.toSSet) a v ⊗
        flagHom (productSpace n factor ⨯ T.toSSet) v b :=
  gateHomProductIso a v b (productCut_necklace_mono_of_nondegenerate n factor T)

/-- The product isomorphism uses the previously constructed actual split. -/
theorem productCutGateHomIso_hom (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a v b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)) :
    (productCutGateHomIso n factor T a v b).hom = productCutGateSplit n factor T a v b := rfl

/-- Its inverse uses the unchanged original composition through the specified vertex. -/
theorem productCutGateHomIso_inv (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a v b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)) :
    (productCutGateHomIso n factor T a v b).inv = gateComposition a v b := rfl

end

end DaggerOriginalProductGadget
