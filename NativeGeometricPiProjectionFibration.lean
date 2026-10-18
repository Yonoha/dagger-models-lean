import NativeGeometricPiVertexPullback

/-! The original-vertex geometric-pi projection is an actual base change of singular based pi. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra
open DaggerNativeGeometricPiVertexPullback DaggerNativeGeometricTotalPiFunctor
open DaggerNativeBasedPiFreeEvaluationPullback (basedProjection)
open SSet.KanComplex
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGeometricPiProjectionFibration
noncomputable section

theorem comparisonMap_app_bijective (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    (k : SimplexCategoryᵒᵖ) : Function.Bijective ((comparisonMap F n).app k) := by
  let q := basedProjection (F ⋙ singularRealization) n
  let v := unitVertexRows F
  constructor
  · rintro ⟨x, s⟩ ⟨y, t⟩ he
    have hx := congrArg (fun w ↦ (pullback.snd q v).app k w) he
    change (comparisonMap F n ≫ pullback.snd q v).app k ⟨x, s⟩ =
      (comparisonMap F n ≫ pullback.snd q v).app k ⟨y, t⟩ at hx
    rw [comparisonMap_snd] at hx
    change x = y at hx
    subst y
    have hc := congrArg (fun w ↦ (pullback.fst q v).app k w) he
    change (comparisonMap F n ≫ pullback.fst q v).app k ⟨x, s⟩ =
      (comparisonMap F n ≫ pullback.fst q v).app k ⟨x, t⟩ at hc
    rw [comparisonMap_fst] at hc
    change (⟨unitVertex (F.obj k) x, s⟩ :
      Σ b : (singularRealization.obj (F.obj k)) _⦋0⦌,
        π n (singularRealization.obj (F.obj k)) b) = ⟨unitVertex (F.obj k) x, t⟩ at hc
    exact Sigma.ext rfl (heq_of_eq (eq_of_heq (Sigma.mk.inj hc).2))
  · intro w
    let x := (pullback.snd q v).app k w
    have hc := congrFun (NatTrans.congr_app (pullback.condition (f := q) (g := v)) k) w
    change q.app k ((pullback.fst q v).app k w) = v.app k x at hc
    generalize hz : (pullback.fst q v).app k w = z at hc
    obtain ⟨b, t⟩ := z
    change b = unitVertex (F.obj k) x at hc
    subst b
    refine ⟨⟨x, t⟩, (FunctorToTypes.pullback_ext).mpr ⟨?_, ?_⟩⟩
    · change (comparisonMap F n ≫ pullback.fst q v).app k ⟨x, t⟩ =
        (pullback.fst q v).app k w
      rw [comparisonMap_fst, hz]
      rfl
    · change (comparisonMap F n ≫ pullback.snd q v).app k ⟨x, t⟩ = x
      rw [comparisonMap_snd]
      rfl

instance comparisonMap_isIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    IsIso (comparisonMap F n) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro k
  exact (isIso_iff_bijective _).mpr (comparisonMap_app_bijective F n k)

def geometricProjectionArrowIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    Arrow.mk (geometricProjection F n) ≅
      Arrow.mk (pullback.snd (basedProjection (F ⋙ singularRealization) n)
        (unitVertexRows F)) :=
  Arrow.isoMk (asIso (comparisonMap F n)) (Iso.refl _) (by
    change _ = geometricProjection F n ≫ 𝟙 _
    rw [Category.comp_id]
    exact comparisonMap_snd F n)

theorem geometricProjection_fibration (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    [Fibration (basedProjection (F ⋙ singularRealization) n)] :
    Fibration (geometricProjection F n) := by
  have hp : Fibration (C := SSet.{u}) (pullback.snd
      (basedProjection (F ⋙ singularRealization) n) (unitVertexRows F)) := inferInstance
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff (geometricProjectionArrowIso F n)).mpr
      ((HomotopicalAlgebra.fibration_iff (C := SSet.{u}) _).mp hp))

end
end DaggerNativeGeometricPiProjectionFibration
