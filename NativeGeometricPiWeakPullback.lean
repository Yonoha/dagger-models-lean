import NativeGeometricPiProjectionFibration

/-! Rowwise weak maps give actual pullbacks of geometric pi over original vertices. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra Opposite
open DaggerNativeGeometricTotalPiFunctor DaggerNativeGeometricPiVertexPullback
open SSet.KanComplex
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGeometricPiWeakPullback
noncomputable section

theorem geometric_mapπ_bijective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : WeakEquivalence f) (n : ℕ) (x : X _⦋0⦌) :
    Function.Bijective (mapπ (singularRealization.map f) n (unitVertex X x)
      (unitVertex Y (f.app _ x)) (unitVertex_natural f x)) := by
  have : WeakEquivalence (SSet.toTop.map f) :=
    (SSet.modelCategoryQuillen.weakEquivalence_iff f).mp hf
  have hs : WeakEquivalence (singularRealization.map f) := by
    change WeakEquivalence (TopCat.toSSet.map (SSet.toTop.map f))
    infer_instance
  exact ((SSet.weakEquivalence_iff_kanComplexW _).mp hs).bijective n _ _ _

def geometricMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G) (n : ℕ) :
    geometricRows F n ⟶ geometricRows G n := Functor.whiskerRight f (geometricPiFunctor n)

def vertexMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G) :
    (F ⋙ SSet.evaluation.obj (op ⦋0⦌) : SSet.{u}) ⟶
      (G ⋙ SSet.evaluation.obj (op ⦋0⦌) : SSet.{u}) :=
  Functor.whiskerRight f (SSet.evaluation.obj (op ⦋0⦌))

theorem geometricMap_projection {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : F ⟶ G) (n : ℕ) : geometricMap f n ≫ geometricProjection G n =
      geometricProjection F n ≫ vertexMap f := by
  apply NatTrans.ext
  rfl

def weakComparison {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G) (n : ℕ) :
    geometricRows F n ⟶ pullback (geometricProjection G n) (vertexMap f) :=
  pullback.lift (geometricMap f n) (geometricProjection F n) (geometricMap_projection f n)

theorem weakComparison_fst {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : F ⟶ G) (n : ℕ) : weakComparison f n ≫
      pullback.fst (geometricProjection G n) (vertexMap f) = geometricMap f n := by
  simp only [weakComparison, pullback.lift_fst]

theorem weakComparison_snd {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : F ⟶ G) (n : ℕ) : weakComparison f n ≫
      pullback.snd (geometricProjection G n) (vertexMap f) = geometricProjection F n := by
  simp only [weakComparison, pullback.lift_snd]

theorem weakComparison_app_bijective {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : F ⟶ G) (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ)
    (k : SimplexCategoryᵒᵖ) : Function.Bijective ((weakComparison f n).app k) := by
  let q := geometricProjection G n
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
    change (⟨(f.app k).app _ x, mapπ (singularRealization.map (f.app k)) n _ _
      (unitVertex_natural (f.app k) x) s⟩ : Σ y : (G.obj k) _⦋0⦌,
        π n (singularRealization.obj (G.obj k)) (unitVertex (G.obj k) y)) =
      ⟨(f.app k).app _ x, mapπ (singularRealization.map (f.app k)) n _ _
        (unitVertex_natural (f.app k) x) t⟩ at hc
    exact Sigma.ext rfl (heq_of_eq
      ((geometric_mapπ_bijective (f.app k) (hf k) n x).injective
        (eq_of_heq (Sigma.mk.inj hc).2)))
  · intro w
    let x := (pullback.snd q v).app k w
    have hc := congrFun (NatTrans.congr_app (pullback.condition (f := q) (g := v)) k) w
    change q.app k ((pullback.fst q v).app k w) = v.app k x at hc
    generalize hz : (pullback.fst q v).app k w = z at hc
    obtain ⟨y, t⟩ := z
    change y = (f.app k).app _ x at hc
    subst y
    obtain ⟨s, hs⟩ := (geometric_mapπ_bijective (f.app k) (hf k) n x).surjective t
    refine ⟨⟨x, s⟩, (FunctorToTypes.pullback_ext).mpr ⟨?_, ?_⟩⟩
    · change (weakComparison f n ≫ pullback.fst q v).app k ⟨x, s⟩ =
        (pullback.fst q v).app k w
      rw [weakComparison_fst, hz]
      exact Sigma.ext rfl (heq_of_eq hs)
    · change (weakComparison f n ≫ pullback.snd q v).app k ⟨x, s⟩ = x
      rw [weakComparison_snd]
      rfl

theorem weakComparison_isIso {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ) : IsIso (weakComparison f n) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro k
  exact (isIso_iff_bijective _).mpr (weakComparison_app_bijective f hf n k)

theorem geometricProjection_fibration_of_rowwise_weak
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ)
    [Fibration (geometricProjection G n)] : Fibration (geometricProjection F n) := by
  have := weakComparison_isIso f hf n
  let i : Arrow.mk (geometricProjection F n) ≅ Arrow.mk
      (pullback.snd (geometricProjection G n) (vertexMap f)) :=
    Arrow.isoMk (asIso (weakComparison f n)) (Iso.refl _) (by
      change _ = geometricProjection F n ≫ 𝟙 _
      rw [Category.comp_id]
      exact weakComparison_snd f n)
  have hp : Fibration (C := SSet.{u})
      (pullback.snd (geometricProjection G n) (vertexMap f)) := inferInstance
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff i).mpr
      ((HomotopicalAlgebra.fibration_iff (C := SSet.{u}) _).mp hp))

end
end DaggerNativeGeometricPiWeakPullback
