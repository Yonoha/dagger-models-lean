import NativeBasedPiFreeEvaluationPullback
import TopCatModelCategory.ModelCategorySSet

/-! Weak maps between Kan rows give literal based-pi pullbacks over original vertices. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra Opposite
open DaggerNativeTotalBasedPiFunctor DaggerNativeBasedPiFreeEvaluationPullback
open SSet.KanComplex
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBasedPiWeakPullback
noncomputable section

theorem based_mapπ_bijective {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) (hf : WeakEquivalence f) (n : ℕ) (x : X _⦋0⦌) :
    Function.Bijective (mapπ f n x (f.app _ x) rfl) :=
  ((SSet.weakEquivalence_iff_kanComplexW f).mp hf).bijective n _ _ _

variable {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}

def basedMap (f : F ⟶ G) (n : ℕ) :
    basedRows F n ⟶ basedRows G n := Functor.whiskerRight f (totalPiFunctor n)

def vertexMap (f : F ⟶ G) :
    (F ⋙ SSet.evaluation.obj (op ⦋0⦌) : SSet.{u}) ⟶
      (G ⋙ SSet.evaluation.obj (op ⦋0⦌) : SSet.{u}) :=
  Functor.whiskerRight f (SSet.evaluation.obj (op ⦋0⦌))

theorem basedMap_projection (f : F ⟶ G) (n : ℕ) : basedMap f n ≫ basedProjection G n =
      basedProjection F n ≫ vertexMap f := by
  apply NatTrans.ext
  rfl

def weakComparison (f : F ⟶ G) (n : ℕ) :
    basedRows F n ⟶ pullback (basedProjection G n) (vertexMap f) :=
  pullback.lift (basedMap f n) (basedProjection F n) (basedMap_projection f n)

theorem weakComparison_fst (f : F ⟶ G) (n : ℕ) : weakComparison f n ≫
      pullback.fst (basedProjection G n) (vertexMap f) = basedMap f n := by
  simp only [weakComparison, pullback.lift_fst]

theorem weakComparison_snd (f : F ⟶ G) (n : ℕ) : weakComparison f n ≫
      pullback.snd (basedProjection G n) (vertexMap f) = basedProjection F n := by
  simp only [weakComparison, pullback.lift_snd]

variable [∀ k, IsFibrant (F.obj k)] [∀ k, IsFibrant (G.obj k)]

theorem weakComparison_app_bijective (f : F ⟶ G) (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ)
    (k : SimplexCategoryᵒᵖ) : Function.Bijective ((weakComparison f n).app k) := by
  let q := basedProjection G n
  let v := vertexMap f
  constructor
  · rintro ⟨x, s⟩ ⟨y, t⟩ he
    have hx := congrArg (fun w ↦ (pullback.snd q v).app k w) he
    change (weakComparison f n ≫ pullback.snd q v).app k ⟨x, s⟩ =
      (weakComparison f n ≫ pullback.snd q v).app k ⟨y, t⟩ at hx
    rw [weakComparison_snd] at hx
    change x = y at hx
    subst y
    have hc := congrArg (fun w ↦ (pullback.fst q v).app k w) he
    change (weakComparison f n ≫ pullback.fst q v).app k ⟨x, s⟩ =
      (weakComparison f n ≫ pullback.fst q v).app k ⟨x, t⟩ at hc
    rw [weakComparison_fst] at hc
    change (⟨(f.app k).app _ x, mapπ (f.app k) n x _ rfl s⟩ : Σ y : (G.obj k) _⦋0⦌,
        π n (G.obj k) y) =
      ⟨(f.app k).app _ x, mapπ (f.app k) n x _ rfl t⟩ at hc
    exact Sigma.ext rfl (heq_of_eq
      ((based_mapπ_bijective (f.app k) (hf k) n x).injective
        (eq_of_heq (Sigma.mk.inj hc).2)))
  · intro w
    let x := (pullback.snd q v).app k w
    have hc := congrFun (NatTrans.congr_app (pullback.condition (f := q) (g := v)) k) w
    change q.app k ((pullback.fst q v).app k w) = v.app k x at hc
    generalize hz : (pullback.fst q v).app k w = z at hc
    obtain ⟨y, t⟩ := z
    change y = (f.app k).app _ x at hc
    subst y
    obtain ⟨s, hs⟩ := (based_mapπ_bijective (f.app k) (hf k) n x).surjective t
    refine ⟨⟨x, s⟩, (FunctorToTypes.pullback_ext).mpr ⟨?_, ?_⟩⟩
    · change (weakComparison f n ≫ pullback.fst q v).app k ⟨x, s⟩ =
        (pullback.fst q v).app k w
      rw [weakComparison_fst, hz]
      exact Sigma.ext rfl (heq_of_eq hs)
    · change (weakComparison f n ≫ pullback.snd q v).app k ⟨x, s⟩ = x
      rw [weakComparison_snd]
      rfl

theorem weakComparison_isIso (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ) : IsIso (weakComparison f n) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro k
  exact (isIso_iff_bijective _).mpr (weakComparison_app_bijective f hf n k)

theorem basedProjection_fibration_of_rowwise_weak
    (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ)
    [Fibration (basedProjection G n)] : Fibration (basedProjection F n) := by
  have := weakComparison_isIso f hf n
  let i : Arrow.mk (basedProjection F n) ≅ Arrow.mk
      (pullback.snd (basedProjection G n) (vertexMap f)) :=
    Arrow.isoMk (asIso (weakComparison f n)) (Iso.refl _) (by
      change _ = basedProjection F n ≫ 𝟙 _
      rw [Category.comp_id]
      exact weakComparison_snd f n)
  have hp : Fibration (C := SSet.{u})
      (pullback.snd (basedProjection G n) (vertexMap f)) := inferInstance
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff i).mpr
      ((HomotopicalAlgebra.fibration_iff (C := SSet.{u}) _).mp hp))

end
end DaggerNativeBasedPiWeakPullback
