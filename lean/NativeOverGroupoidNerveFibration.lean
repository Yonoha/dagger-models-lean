import NativeOverNerveSimplexFamily

/-! The native over-forgetful nerve over a groupoid is a genuine Kan-model fibration. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open HomotopicalAlgebra DaggerUnitaryDiscrete
open DaggerNativeOverChainDecomposition DaggerNativeOverChainFixedProjection
open DaggerNativeSimplexPullbackFibrationDetection DaggerNativeOverNerveSimplexFamily
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOverGroupoidNerveFibration
noncomputable section

theorem simplexFamily_app_isPullback {G : Type u} [Groupoid.{u} G] (z : G) {n : ℕ}
    (A : Fin (n + 1) ⥤ G) (v : SimplexCategoryᵒᵖ) :
    IsPullback ((simplexFamily z A).app v)
      ((fst (Δ[n] : SSet.{u}) (constSSet (A.obj (Fin.last n) ⟶ z))).app v)
      ((nerveMap (Over.forget z)).app v) ((SSet.yonedaEquiv.symm A).app v) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (simplexFamily_projection z A) v, ?_, ?_⟩
  · rintro ⟨t, f⟩ ⟨s, g⟩ ⟨hf, ht⟩
    change t = s at ht
    subst s
    apply Prod.ext
    · rfl
    · apply (cancel_epi (lastArrow A t)).mp
      exact chainLift_injective (restrictChain A t) hf
  · intro B t h
    have hb : B ⋙ Over.forget z = restrictChain A t := h
    obtain ⟨f, hf⟩ := chainLift_surjective_on_fibre (restrictChain A t) B hb
    refine ⟨(t, inv (lastArrow A t) ≫ f), ?_, rfl⟩
    change chainLift (restrictChain A t) (lastArrow A t ≫ inv (lastArrow A t) ≫ f) = B
    simpa using hf

theorem simplexFamily_isPullback {G : Type u} [Groupoid.{u} G] (z : G) {n : ℕ}
    (A : Fin (n + 1) ⥤ G) :
    IsPullback (simplexFamily z A)
      (fst (Δ[n] : SSet.{u}) (constSSet (A.obj (Fin.last n) ⟶ z)))
      (nerveMap (Over.forget z)) (SSet.yonedaEquiv.symm A) := by
  let c := PullbackCone.mk (simplexFamily z A)
    (fst (Δ[n] : SSet.{u}) (constSSet (A.obj (Fin.last n) ⟶ z)))
    (simplexFamily_projection z A)
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro v
  let h := simplexFamily_app_isPullback z A v
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

def simplexPullbackIso {G : Type u} [Groupoid.{u} G] (z : G) {n : ℕ}
    (A : Fin (n + 1) ⥤ G) :
    (Δ[n] : SSet.{u}) ⊗ constSSet (A.obj (Fin.last n) ⟶ z) ≅
      pullback (nerveMap (Over.forget z))
        ((SSet.yonedaEquiv (X := nerve G) (n := ⦋n⦌)).symm A) :=
  (simplexFamily_isPullback z A).isoPullback

theorem over_forget_nerve_fibration (G : Type u) [Groupoid.{u} G] (z : G) :
    Fibration (nerveMap (Over.forget z)) := by
  apply fibration_of_simplex_pullbacks
  intro n b
  let A : Fin (n + 1) ⥤ G := SSet.yonedaEquiv b
  have hb : SSet.yonedaEquiv.symm A = b := SSet.yonedaEquiv.symm_apply_apply b
  rw [← hb]
  have : (constSSet (A.obj (Fin.last n) ⟶ z)).KanComplex := constSSet_fibrant _
  have : Fibration (fst (Δ[n] : SSet.{u}) (constSSet (A.obj (Fin.last n) ⟶ z))) :=
    product_projection_fibration _ _
  let e := simplexPullbackIso z A
  let a : Arrow.mk (fst (Δ[n] : SSet.{u}) (constSSet (A.obj (Fin.last n) ⟶ z))) ≅
      Arrow.mk (pullback.snd (nerveMap (Over.forget z))
        ((SSet.yonedaEquiv (X := nerve G) (n := ⦋n⦌)).symm A)) :=
    Arrow.isoMk e (Iso.refl _) (by
      exact (simplexFamily_isPullback z A).isoPullback_hom_snd)
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact ((fibrations SSet.{u}).arrow_mk_iso_iff a).mp
    ((HomotopicalAlgebra.fibration_iff _).mp inferInstance)

end
end DaggerNativeOverGroupoidNerveFibration
