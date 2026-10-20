import NativeSSetCoproductSummandFibration
import NativeSSetCoproductHomotopy
import SSetRightProper
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Detecting the actual original component maps of a weak simplicial coproduct map

The original index is retained. Each actual component square is a native
pullback, and its target summand inclusion is an unconditional Kan fibration.
The retained right-properness theorem therefore reflects weakness to every
unchanged original component, including empty simplicial sets.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open DaggerNativeSSetCoproductHomotopy DaggerNativeSSetCoproductSummandFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSSetCoproductComponentWeakEquivalence
noncomputable section

/-- In every degree, the unchanged component square is the actual pullback of the whole map. -/
theorem coproductComponent_app_isPullback {I : Type u} {X Y : I → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) (i : I) (n : SimplexCategoryᵒᵖ) :
    IsPullback ((f i).app n) ((Sigma.ι X i).app n)
      ((Sigma.ι Y i).app n) ((Limits.Sigma.map f).app n) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (Sigma.ι_map f i).symm n, ?_, ?_⟩
  · intro a b h
    exact eq_of_heq (Sigma.mk.inj
      ((coproductDegreeEquiv X n).injective h.2)).2
  · intro y a h
    obtain ⟨⟨j, x⟩, rfl⟩ := (coproductDegreeEquiv X n).surjective a
    change coproductDegreeEquiv Y n ⟨i, y⟩ =
      (Limits.Sigma.map f).app n (coproductDegreeEquiv X n ⟨j, x⟩) at h
    rw [coproductMap_apply] at h
    have hs := (coproductDegreeEquiv Y n).injective h
    have hj : j = i := (Sigma.mk.inj hs).1.symm
    subst j
    exact ⟨x, (eq_of_heq (Sigma.mk.inj hs).2).symm, rfl⟩

/-- The entire original simplicial component square is an actual native pullback. -/
theorem coproductComponent_isPullback {I : Type u} {X Y : I → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) (i : I) :
    IsPullback (f i) (Sigma.ι X i) (Sigma.ι Y i) (Limits.Sigma.map f) := by
  let c := PullbackCone.mk (f i) (Sigma.ι X i) (Sigma.ι_map f i).symm
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro n
  let h := coproductComponent_app_isPullback f i n
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

/-- Weakness of the whole index-preserving coproduct map implies weakness of every actual map. -/
theorem coproductComponent_weakEquivalence {I : Type u} {X Y : I → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) (h : WeakEquivalence (Limits.Sigma.map f)) (i : I) :
    WeakEquivalence (f i) := by
  have := coproductSummand_fibration Y i
  have := h
  exact DaggerSSetRightProper.weakEquivalence_of_isPullback
    (coproductComponent_isPullback f i)

end
end DaggerNativeSSetCoproductComponentWeakEquivalence
