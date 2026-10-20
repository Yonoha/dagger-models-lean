import OriginalProductNecklaceCut
import ChosenNecklaceTargetJoints

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

def productJointInclusion (K : SSet.{u}) (T : NecklaceCode) (j : Fin (T.len + 1)) :
    K ⨯ (Δ[0] : SSet.{u}) ⟶ K ⨯ T.toSSet :=
  prod.map (𝟙 K) (pointAt T (ULift.up j))

def productCrossingPoint (K : SSet.{u}) (T S : NecklaceCode)
    (f : S.toSSet ⟶ K ⨯ T.toSSet) (k : Fin (S.len + 1)) :
    (Δ[0] : SSet.{u}) ⟶ K ⨯ (Δ[0] : SSet.{u}) :=
  prod.lift (pointAt S (ULift.up k) ≫ f ≫ prod.fst) (𝟙 _)

/-- The source vertex over the target joint factors through the actual common product. -/
theorem productCrossingPoint_fac (K : SSet.{u}) (T S : NecklaceCode)
    (f : S.toSSet ⟶ K ⨯ T.toSSet) (k : Fin (S.len + 1)) (j : Fin (T.len + 1))
    (hk : orderMap (f ≫ prod.snd) k = j) :
    productCrossingPoint K T S f k ≫ productJointInclusion K T j =
      pointAt S (ULift.up k) ≫ f := by
  apply prod.hom_ext
  · simp [productCrossingPoint, productJointInclusion, Category.assoc]
  · have he : mapVertices (f ≫ prod.snd) (ULift.up k) = ULift.up j := ULift.ext _ _ hk
    have hp := pointAt_comp (ULift.up k) (f ≫ prod.snd)
    rw [he] at hp
    simpa [productCrossingPoint, productJointInclusion, Category.assoc] using hp.symm

def productNecklaceCoordinate (K : SSet.{u}) (T : NecklaceCode)
    (x : (K ⨯ T.toSSet).obj (op ⦋0⦌)) : Fin (T.len + 1) :=
  (T.verticesEquiv ((prod.snd : K ⨯ T.toSSet ⟶ T.toSSet).app _ x)).down

/-- Every original crossing necklace hits the common product at one of its actual joints. -/
theorem productOver_crossingJoint (K : SSet.{u}) (T : NecklaceCode)
    {a b : (K ⨯ T.toSSet).obj (op ⦋0⦌)} (P : NecklacesOver (K ⨯ T.toSSet) a b)
    (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (ha : productNecklaceCoordinate K T a ≤ j)
    (hb : j ≤ productNecklaceCoordinate K T b) :
    ∃ k ∈ P.code.joints, orderMap (P.map ≫ prod.snd) k = j ∧
      productCrossingPoint K T P.code P.map k ≫ productJointInclusion K T j =
        pointAt P.code (ULift.up k) ≫ P.map := by
  obtain ⟨k, hk, he⟩ := original_over_target_joint
    ((NecklacesOver.postcomp (prod.snd : K ⨯ T.toSSet ⟶ T.toSSet)).obj P) j hj ha hb
  exact ⟨k, hk, he, productCrossingPoint_fac K T P.code P.map k j he⟩

end

end DaggerOriginalProductGadget
