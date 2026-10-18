import NativeBasedPiFreeEvaluationPullback

/-! The literal total based-pi projection is a pullback of the actual free-sphere evaluation. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial
open DaggerNativeBasedPiFreeEvaluationPullback DaggerNativeSimpleSphereFreeClasses
open DaggerNativeMappingEvaluationRealizationUnit DaggerNativeUnitalMultiplicationAction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBasedPiProjectionFibration
noncomputable section

variable (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) (i : Fin (n + 2))
  (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
  [∀ k, IsFibrant (F.obj k)] (hS : ∀ k x, TrivialActionAt (F.obj k) x)

theorem comparisonMap_app_bijective (k : SimplexCategoryᵒᵖ) :
    Function.Bijective ((comparisonMap F n i a hS).app k) := by
  let q := rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))
  let v := vertexComponents F
  constructor
  · rintro ⟨x, s⟩ ⟨y, t⟩ he
    have hx := congrArg (fun w ↦ (pullback.snd q v).app k w) he
    change (comparisonMap F n i a hS ≫ pullback.snd q v).app k ⟨x, s⟩ =
      (comparisonMap F n i a hS ≫ pullback.snd q v).app k ⟨y, t⟩ at hx
    rw [comparisonMap_snd] at hx
    change x = y at hx
    subst y
    have hc := congrArg (fun w ↦ (pullback.fst q v).app k w) he
    change (comparisonMap F n i a hS ≫ pullback.fst q v).app k ⟨x, s⟩ =
      (comparisonMap F n i a hS ≫ pullback.fst q v).app k ⟨x, t⟩ at hc
    rw [comparisonMap_fst] at hc
    change (piFreeSphereFibreEquiv n i a (F.obj k) x (hS k x) s).val =
      (piFreeSphereFibreEquiv n i a (F.obj k) x (hS k x) t).val at hc
    exact Sigma.ext rfl (heq_of_eq
      ((piFreeSphereFibreEquiv n i a (F.obj k) x (hS k x)).injective (Subtype.ext hc)))
  · intro w
    let x := (pullback.snd q v).app k w
    let c := (pullback.fst q v).app k w
    have hc : SSet.mapπ₀ (DaggerOriginalFixedObjectCotensorPoints.pointEvaluation
        (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) (F.obj k)) c =
          SSet.π₀.mk x :=
      congrFun (NatTrans.congr_app (pullback.condition (f := q) (g := v)) k) w
    let e := piFreeSphereFibreEquiv n i a (F.obj k) x (hS k x)
    let s := e.symm ⟨c, hc⟩
    refine ⟨⟨x, s⟩, (FunctorToTypes.pullback_ext).mpr ⟨?_, ?_⟩⟩
    · change (comparisonMap F n i a hS ≫ pullback.fst q v).app k ⟨x, s⟩ = c
      rw [comparisonMap_fst]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨c, hc⟩)
    · change (comparisonMap F n i a hS ≫ pullback.snd q v).app k ⟨x, s⟩ = x
      rw [comparisonMap_snd]
      rfl

instance comparisonMap_isIso : IsIso (comparisonMap F n i a hS) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro k
  exact (isIso_iff_bijective _).mpr (comparisonMap_app_bijective F n i a hS k)

def basedProjectionArrowIso : Arrow.mk (basedProjection F n) ≅
    Arrow.mk (pullback.snd
      (rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)))
      (vertexComponents F)) :=
  Arrow.isoMk (asIso (comparisonMap F n i a hS)) (Iso.refl _) (by
    change _ = basedProjection F n ≫ 𝟙 _
    rw [Category.comp_id]
    exact comparisonMap_snd F n i a hS)

include hS in
theorem basedProjection_fibration
    [Fibration (C := SSet.{u})
      (rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)))] :
    Fibration (basedProjection F n) := by
  have hp : Fibration (C := SSet.{u}) (pullback.snd
      (rowEvaluation F (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)))
      (vertexComponents F)) := inferInstance
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff (basedProjectionArrowIso F n i a hS)).mpr
      ((HomotopicalAlgebra.fibration_iff (C := SSet.{u}) _).mp hp))

end
end DaggerNativeBasedPiProjectionFibration
