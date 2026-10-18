import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! Apply Mathlib's existing Types pushout criterion to an actual subcomplex attachment.
All hypotheses below must be discharged for each of the four original amalgam families. -/

open CategoryTheory Limits

universe u

set_option autoImplicit false

namespace DaggerAmalgamAttachment

noncomputable section

variable {H T : SSet.{u}} (S S' : H.Subcomplex) (hSS : S ≤ S')
  (D : T.Subcomplex) (e : T ⟶ H) (he : SSet.Subcomplex.range e ≤ S')
  (hD : ∀ (q : SimplexCategoryᵒᵖ) (v : T.obj q), e.app q v ∈ S.obj q ↔ v ∈ D.obj q)

def toStage : T ⟶ (S' : SSet.{u}) := SSet.Subcomplex.lift e he

def boundaryToStage : (D : SSet.{u}) ⟶ (S : SSet.{u}) :=
  SSet.Subcomplex.lift (D.ι ≫ e) (by
    intro q h hh
    obtain ⟨w, rfl⟩ := hh
    exact (hD q w.val).2 w.property)

theorem commutes :
    boundaryToStage S D e hD ≫ SSet.Subcomplex.homOfLE hSS = D.ι ≫ toStage S' e he := by
  ext q w
  rfl

/-- Exact boundary preimage gives the full degreewise pullback, on original tuples. -/
theorem app_isPullback (q : SimplexCategoryᵒᵖ) :
    IsPullback ((boundaryToStage S D e hD).app q) (D.ι.app q)
      ((SSet.Subcomplex.homOfLE hSS).app q) ((toStage S' e he).app q) := by
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (commutes S S' hSS D e he hD) q, ?_, ?_⟩
  · intro v w hvw
    exact Subtype.ext hvw.2
  · intro z w heq
    have hv := congrArg Subtype.val heq
    change z.val = e.app q w at hv
    have hw : w ∈ D.obj q := (hD q w).1 (hv ▸ z.property)
    exact ⟨⟨w, hw⟩, Subtype.ext hv.symm, rfl⟩

variable
  (coverage : ∀ (q : SimplexCategoryᵒᵖ) (z : (S' : SSet.{u}).obj q),
    z.val ∈ S.obj q ∨ ∃ w : T.obj q, e.app q w = z.val)
  (interior_injective : ∀ (q : SimplexCategoryᵒᵖ) (v w : T.obj q),
    v ∉ D.obj q → w ∉ D.obj q → e.app q v = e.app q w → v = w)

include coverage interior_injective

theorem app_isPushout (q : SimplexCategoryᵒᵖ) :
    IsPushout ((boundaryToStage S D e hD).app q) (D.ι.app q)
      ((SSet.Subcomplex.homOfLE hSS).app q) ((toStage S' e he).app q) := by
  apply Types.isPushout_of_isPullback_of_mono' (app_isPullback S S' hSS D e he hD q)
  · apply Set.eq_univ_of_forall
    intro z
    obtain hz | ⟨w, hw⟩ := coverage q z
    · exact Or.inl ⟨⟨z.val, hz⟩, rfl⟩
    · exact Or.inr ⟨w, Subtype.ext hw⟩
  · intro v w hv hw heq
    exact interior_injective q v w (fun h ↦ hv ⟨⟨v, h⟩, rfl⟩)
      (fun h ↦ hw ⟨⟨w, h⟩, rfl⟩) (congrArg Subtype.val heq)

/-- Evaluation reflection supplies the unrestricted simplicial pushout universal property. -/
theorem isPushout :
    IsPushout (boundaryToStage S D e hD) D.ι (SSet.Subcomplex.homOfLE hSS)
      (toStage S' e he) := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk (SSet.Subcomplex.homOfLE hSS) (toStage S' e he)
      (commutes S S' hSS D e he hD))
  apply evaluationJointlyReflectsColimits
  intro q
  exact (isColimitMapCoconePushoutCoconeEquiv ((evaluation _ (Type u)).obj q)
    (commutes S S' hSS D e he hD)).symm
      (app_isPushout S S' hSS D e he hD coverage interior_injective q).isColimit

end
end DaggerAmalgamAttachment
