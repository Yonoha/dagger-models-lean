import NativeFibrewiseWeakRecognition
import NativeSimplexPullbackFibrationDetection

/-! Exact base change of the original pointwise product projection. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open HomotopicalAlgebra DaggerNativeSSetFibrationsOverBaseWeakPullbacks
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeProductProjectionBaseChange
noncomputable section

theorem productBaseChange_app_isPullback {V K : SSet.{u}} (b : V ⟶ K)
    (X : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    IsPullback ((b ⊗ₘ 𝟙 X).app n) ((fst V X).app n) ((fst K X).app n) (b.app n) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨v, x⟩ ⟨w, y⟩ ⟨h₁, h₂⟩
    change (b.app n v, x) = (b.app n w, y) at h₁
    exact Prod.ext h₂ (congrArg (fun p : K.obj n × X.obj n ↦ p.2) h₁)
  · rintro ⟨k, x⟩ v h
    exact ⟨(v, x), Prod.ext h.symm rfl, rfl⟩

theorem productBaseChange_isPullback {V K : SSet.{u}} (b : V ⟶ K) (X : SSet.{u}) :
    IsPullback (b ⊗ₘ 𝟙 X) (fst V X) (fst K X) b := by
  have hw : (b ⊗ₘ 𝟙 X) ≫ fst K X = fst V X ≫ b := by
    apply NatTrans.ext
    rfl
  let c : PullbackCone (fst K X) b := PullbackCone.mk (b ⊗ₘ 𝟙 X) (fst V X) hw
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro n
  let h := productBaseChange_app_isPullback b X n
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

def productBaseChangeIso {V K : SSet.{u}} (b : V ⟶ K) (X : SSet.{u}) :
    V ⊗ X ≅ pullback (fst K X) b := (productBaseChange_isPullback b X).isoPullback

theorem productBaseChangeIso_hom_fst {V K : SSet.{u}} (b : V ⟶ K) (X : SSet.{u}) :
    (productBaseChangeIso b X).hom ≫ pullback.fst (fst K X) b = b ⊗ₘ 𝟙 X :=
  (productBaseChange_isPullback b X).isoPullback_hom_fst

theorem productBaseChangeIso_hom_snd {V K : SSet.{u}} (b : V ⟶ K) (X : SSet.{u}) :
    (productBaseChangeIso b X).hom ≫ pullback.snd (fst K X) b = fst V X :=
  (productBaseChange_isPullback b X).isoPullback_hom_snd

theorem productBaseChangeIso_map {V K X Y : SSet.{u}} (b : V ⟶ K)
    (f : K ⊗ X ⟶ K ⊗ Y) (h : f ≫ fst K Y = fst K X)
    (g : V ⊗ X ⟶ V ⊗ Y) (hg : g ≫ fst V Y = fst V X)
    (hb : (b ⊗ₘ 𝟙 X) ≫ f = g ≫ (b ⊗ₘ 𝟙 Y)) :
    (productBaseChangeIso b X).hom ≫ mapOver (fst K X) (fst K Y) f h b =
      g ≫ (productBaseChangeIso b Y).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, mapOver_fst, ← Category.assoc,
      productBaseChangeIso_hom_fst, Category.assoc, productBaseChangeIso_hom_fst]
    exact hb
  · have hs : mapOver (fst K X) (fst K Y) f h b ≫ pullback.snd (fst K Y) b =
        pullback.snd (fst K X) b := by simp [mapOver]
    rw [Category.assoc, hs, productBaseChangeIso_hom_snd,
      Category.assoc, productBaseChangeIso_hom_snd, hg]

end
end DaggerNativeProductProjectionBaseChange
