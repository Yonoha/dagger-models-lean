import OriginalProductCrossingJoint
import OriginalNecklaceIntervalRestriction

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable (K : SSet.{u}) (T S : NecklaceCode) (f : S.toSSet ⟶ K ⨯ T.toSSet)
  (k : Fin (S.len + 1)) (j : Fin (T.len + 1))
  (hk : orderMap (f ≫ prod.snd) k = j)

/-- The actual prefix of the source maps into the actual prefix of the target necklace factor. -/
def productCrossingLeftLift : (cutLeft S k).toSSet ⟶ K ⨯ (cutLeft T j).toSSet :=
  prod.lift (cutLeftι S k ≫ f ≫ prod.fst)
    (necklaceIntervalMap (f ≫ prod.snd) 0 k (Fin.zero_le k) 0 j (Fin.zero_le j)
      (Fin.zero_le _) hk.le)

/-- The actual suffix of the source maps into the actual suffix of the target necklace factor. -/
def productCrossingRightLift : (cutRight S k).toSSet ⟶ K ⨯ (cutRight T j).toSSet :=
  prod.lift (cutRightι S k ≫ f ≫ prod.fst)
    (necklaceIntervalMap (f ≫ prod.snd) k (Fin.last S.len) (Fin.le_last k)
      j (Fin.last T.len) (Fin.le_last j) hk.ge (Fin.le_last _))

theorem productCrossingLeft_fac :
    productCrossingLeftLift K T S f k j hk ≫ prod.map (𝟙 K) (cutLeftι T j) =
      cutLeftι S k ≫ f := by
  apply prod.hom_ext
  · simp [productCrossingLeftLift, Category.assoc]
  · simp only [Category.assoc, prod.map_snd, productCrossingLeftLift, prod.lift_snd_assoc]
    exact necklaceIntervalMap_fac (f ≫ prod.snd) 0 k (Fin.zero_le k)
      0 j (Fin.zero_le j) (Fin.zero_le _) hk.le

theorem productCrossingRight_fac :
    productCrossingRightLift K T S f k j hk ≫ prod.map (𝟙 K) (cutRightι T j) =
      cutRightι S k ≫ f := by
  apply prod.hom_ext
  · simp [productCrossingRightLift, Category.assoc]
  · simp only [Category.assoc, prod.map_snd, productCrossingRightLift, prod.lift_snd_assoc]
    exact necklaceIntervalMap_fac (f ≫ prod.snd) k (Fin.last S.len) (Fin.le_last k)
      j (Fin.last T.len) (Fin.le_last j) hk.ge (Fin.le_last _)

/-- The two original restrictions agree on the source's actual common joint. -/
theorem productCrossing_compatible :
    pointAt (cutLeft S k) (ULift.up (Fin.last _)) ≫
      (productCrossingLeftLift K T S f k j hk ≫ prod.map (𝟙 K) (cutLeftι T j)) =
    pointAt (cutRight S k) (ULift.up 0) ≫
      (productCrossingRightLift K T S f k j hk ≫ prod.map (𝟙 K) (cutRightι T j)) := by
  rw [productCrossingLeft_fac, productCrossingRight_fac, ← Category.assoc,
    cut_comm, Category.assoc]

/-- Gluing the two factors along that joint recovers the entire supplied map f. -/
theorem productCrossing_glue (hkJ : k ∈ S.joints) :
    (cutIsPushout S k hkJ).desc
      (productCrossingLeftLift K T S f k j hk ≫ prod.map (𝟙 K) (cutLeftι T j))
      (productCrossingRightLift K T S f k j hk ≫ prod.map (𝟙 K) (cutRightι T j))
      (productCrossing_compatible K T S f k j hk) = f := by
  apply (cutIsPushout S k hkJ).hom_ext
  · rw [IsPushout.inl_desc, productCrossingLeft_fac]
  · rw [IsPushout.inr_desc, productCrossingRight_fac]

end

end DaggerOriginalProductGadget
