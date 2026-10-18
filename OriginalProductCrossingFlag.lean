import OriginalFlagCutComposition

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- A crossing flag has an actual source-joint split, lifts into both target sides,
meets at the same common-product point, and represents the original flag composition.
No functorial choice of this joint is asserted. -/
theorem productFlag_crossing_factorization (K : SSet.{u}) (T : NecklaceCode)
    {a b : (K ⨯ T.toSSet).obj (op ⦋0⦌)} (P : NecklacesOver (K ⨯ T.toSSet) a b)
    (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (ha : productNecklaceCoordinate K T a ≤ j)
    (hb : j ≤ productNecklaceCoordinate K T b)
    {n : ℕ} (F : Flag.{u} P.code n) :
    ∃ (k : Fin (P.code.len + 1)) (hk : k ∈ P.code.joints)
      (FL : Flag.{u} (cutLeft P.code k) n) (FR : Flag.{u} (cutRight P.code k) n)
      (L : (cutLeft P.code k).toSSet ⟶ K ⨯ (cutLeft T j).toSSet)
      (R : (cutRight P.code k).toSSet ⟶ K ⨯ (cutRight T j).toSSet),
      orderMap (P.map ≫ prod.snd) k = j ∧
      L ≫ prod.map (𝟙 K) (cutLeftι T j) = (cutLeftOver P k).map ∧
      R ≫ prod.map (𝟙 K) (cutRightι T j) = (cutRightOver P k).map ∧
      pointAt (cutLeft P.code k) (ULift.up (Fin.last _)) ≫ L =
        productCrossingPoint K T P.code P.map k ≫
          prod.map (𝟙 K) (pointAt (cutLeft T j) (ULift.up (Fin.last _))) ∧
      pointAt (cutRight P.code k) (ULift.up 0) ≫ R =
        productCrossingPoint K T P.code P.map k ≫
          prod.map (𝟙 K) (pointAt (cutRight T j) (ULift.up 0)) ∧
      (FL, FR) = (cutFlagIso P.code k hk).hom.app (op ⦋n⦌) F ∧
      flagCompApp
          (Quot.mk _ (⟨cutLeftOver P k, FL⟩ : RawFlag _ a _ (op ⦋n⦌)))
          (Quot.mk _ (⟨cutRightOver P k, FR⟩ : RawFlag _ _ b (op ⦋n⦌))) =
        Quot.mk _ (⟨P, F⟩ : RawFlag _ a b (op ⦋n⦌)) := by
  obtain ⟨k, hk, he, _⟩ := productOver_crossingJoint K T P j hj ha hb
  refine ⟨k, hk, ((cutFlagIso P.code k hk).hom.app (op ⦋n⦌) F).1,
    ((cutFlagIso P.code k hk).hom.app (op ⦋n⦌) F).2,
    productCrossingLeftLift K T P.code P.map k j he,
    productCrossingRightLift K T P.code P.map k j he, he,
    productCrossingLeft_fac K T P.code P.map k j he,
    productCrossingRight_fac K T P.code P.map k j he,
    productCrossingLeft_joint K T P.code P.map k j he,
    productCrossingRight_joint K T P.code P.map k j he, rfl, flagComp_cut P k hk F⟩

end

end DaggerOriginalProductGadget
