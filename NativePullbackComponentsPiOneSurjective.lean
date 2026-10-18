import NativePiOneSurjectiveFibreComponents

/-! Actual components of a pullback when one leg is a fibration surjective on pi one. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativePiOneSurjectiveFibreComponents
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePullbackComponentsPiOneSurjective
noncomputable section

def componentsComparison {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B) :
    (pullback p q).π₀ →
      {a : E.π₀ × C.π₀ // mapπ₀ p a.1 = mapπ₀ q a.2} :=
  fun s ↦ ⟨(mapπ₀ (pullback.fst p q) s, mapπ₀ (pullback.snd p q) s), by
    rw [← mapπ₀_comp_apply, pullback.condition, mapπ₀_comp_apply]⟩

def pullbackVertex {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (e : E _⦋0⦌) (c : C _⦋0⦌) (h : p.app _ e = q.app _ c) :
    (pullback p q) _⦋0⦌ :=
  yonedaEquiv (pullback.lift (yonedaEquiv.symm e) (yonedaEquiv.symm c) (by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h))

theorem pullbackVertex_fst {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (e : E _⦋0⦌) (c : C _⦋0⦌) (h : p.app _ e = q.app _ c) :
    (pullback.fst p q).app _ (pullbackVertex p q e c h) = e := by
  dsimp only [pullbackVertex]
  rw [← yonedaEquiv_comp, pullback.lift_fst]
  exact Equiv.apply_symm_apply _ e

theorem pullbackVertex_snd {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (e : E _⦋0⦌) (c : C _⦋0⦌) (h : p.app _ e = q.app _ c) :
    (pullback.snd p q).app _ (pullbackVertex p q e c h) = c := by
  dsimp only [pullbackVertex]
  rw [← yonedaEquiv_comp, pullback.lift_snd]
  exact Equiv.apply_symm_apply _ c

def fibreToPullback {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B) (c : C _⦋0⦌) :
    (Subcomplex.fiber p (q.app _ c) : SSet.{u}) ⟶ pullback p q :=
  pullback.lift (Subcomplex.fiber p (q.app _ c)).ι (SSet.const c) (by
    rw [Subcomplex.fiber_ι_comp, SSet.const_comp])

def fibreVertex {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B) (c : C _⦋0⦌)
    (w : (pullback p q) _⦋0⦌) (hc : (pullback.snd p q).app _ w = c) :
    (Subcomplex.fiber p (q.app _ c) : SSet.{u}) _⦋0⦌ :=
  ⟨(pullback.fst p q).app _ w, by
    rw [Subcomplex.mem_fiber_obj_zero_iff]
    have hh := congrFun (NatTrans.congr_app (pullback.condition (f := p) (g := q)) _) w
    change p.app _ ((pullback.fst p q).app _ w) = q.app _ ((pullback.snd p q).app _ w) at hh
    exact hh.trans (congrArg (q.app _) hc)⟩

theorem fibreToPullback_fibreVertex {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    (c : C _⦋0⦌) (w : (pullback p q) _⦋0⦌) (hc : (pullback.snd p q).app _ w = c) :
    (fibreToPullback p q c).app _ (fibreVertex p q c w hc) = w := by
  apply FunctorToTypes.pullback_ext.mpr
  constructor
  · change (fibreToPullback p q c ≫ pullback.fst p q).app _ _ = _
    simp only [fibreToPullback, pullback.lift_fst]
    rfl
  · change (fibreToPullback p q c ≫ pullback.snd p q).app _ _ = _
    simp only [fibreToPullback, pullback.lift_snd]
    simpa only [SSet.const_app, SimplexCategory.const_eq_id, op_id,
      FunctorToTypes.map_id_apply] using hc.symm

theorem componentsComparison_surjective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] : Function.Surjective (componentsComparison p q) := by
  have : IsFibrant E := isFibrant_of_fibration p
  rintro ⟨⟨u, v⟩, huv⟩
  obtain ⟨e, rfl⟩ := π₀.mk_surjective u
  obtain ⟨c, rfl⟩ := π₀.mk_surjective v
  change π₀.mk (p.app _ e) = π₀.mk (q.app _ c) at huv
  obtain ⟨path⟩ := (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff _ _).mp huv
  obtain ⟨e', ⟨he⟩⟩ := FiberActionStruct.nonempty p path e rfl
  refine ⟨π₀.mk (pullbackVertex p q e' c he.app_one), Subtype.ext ?_⟩
  apply Prod.ext
  · change π₀.mk ((pullback.fst p q).app _ _) = π₀.mk e
    rw [pullbackVertex_fst]
    symm
    apply (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff _ _).mpr
    exact ⟨Edge.mk he.map he.δ₁_map he.δ₀_map⟩
  · change π₀.mk ((pullback.snd p q).app _ _) = π₀.mk c
    rw [pullbackVertex_snd]

theorem componentsComparison_injective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] [IsFibrant C]
    (hp : ∀ (e : E _⦋0⦌) (b : B _⦋0⦌) (he : p.app _ e = b),
      Function.Surjective (mapπ p 1 e b he)) :
    Function.Injective (componentsComparison p q) := by
  have : Fibration (pullback.snd p q) := inferInstance
  have : IsFibrant (pullback p q) := isFibrant_of_fibration (pullback.snd p q)
  intro u v h
  obtain ⟨w, rfl⟩ := π₀.mk_surjective u
  obtain ⟨w', rfl⟩ := π₀.mk_surjective v
  have hc : π₀.mk ((pullback.snd p q).app _ w) =
      π₀.mk ((pullback.snd p q).app _ w') := congrArg (fun a ↦ a.val.2) h
  have he : π₀.mk ((pullback.fst p q).app _ w) =
      π₀.mk ((pullback.fst p q).app _ w') := congrArg (fun a ↦ a.val.1) h
  obtain ⟨path⟩ := (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff _ _).mp hc
  obtain ⟨z, ⟨hz⟩⟩ := FiberActionStruct.nonempty (pullback.snd p q) path w rfl
  have hwz : π₀.mk w = π₀.mk z := by
    apply (SSet.KanComplex.π₀_mk_eq_π₀_mk_iff _ _).mpr
    exact ⟨Edge.mk hz.map hz.δ₁_map hz.δ₀_map⟩
  have hez : π₀.mk ((pullback.fst p q).app _ z) =
      π₀.mk ((pullback.fst p q).app _ w') :=
    (congrArg (mapπ₀ (pullback.fst p q)) hwz).symm.trans he
  let c := (pullback.snd p q).app _ w'
  have hzf : π₀.mk (fibreVertex p q c z hz.app_one) =
      π₀.mk (fibreVertex p q c w' rfl) :=
    fibre_inclusion_components_injective_of_pi_one_surjective p hp (q.app _ c) hez
  have hh := congrArg (mapπ₀ (fibreToPullback p q c)) hzf
  change π₀.mk ((fibreToPullback p q c).app _ (fibreVertex p q c z hz.app_one)) =
    π₀.mk ((fibreToPullback p q c).app _ (fibreVertex p q c w' rfl)) at hh
  rw [fibreToPullback_fibreVertex, fibreToPullback_fibreVertex] at hh
  exact hwz.trans hh

theorem componentsComparison_bijective {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B)
    [Fibration p] [IsFibrant B] [IsFibrant C]
    (hp : ∀ (e : E _⦋0⦌) (b : B _⦋0⦌) (he : p.app _ e = b),
      Function.Surjective (mapπ p 1 e b he)) :
    Function.Bijective (componentsComparison p q) :=
  ⟨componentsComparison_injective p q hp, componentsComparison_surjective p q⟩

end
end DaggerNativePullbackComponentsPiOneSurjective
