import DaggerModels.FreeCofibration
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
# Stability of free cofibrations under transfinite composition

This proves the transfinite-composition closure in Part I, `dj.lem.free-cof`.
The diagram is well-order-continuous in mathlib's sense. Its transition maps
and colimit inclusions are monomorphisms. Induction on the stages shows that
every fixed nondegenerate positive-dimensional simplex already comes from
the bottom stage; at limit stages this uses the actual colimit cocone.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.DaggerSSet

private theorem sSet_monomorphisms_stable (J : Type u) [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] :
    (MorphismProperty.monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape J := by
  change (MorphismProperty.monomorphisms
    (SimplexCategoryᵒᵖ ⥤ Type u)).IsStableUnderTransfiniteCompositionOfShape J
  infer_instance

private theorem mono_of_transfinite {J : Type u} [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (h : MorphismProperty.TransfiniteCompositionOfShape
      (fun _ _ f ↦ FreeCofibration f) J f) : Mono f := by
  let : PreservesColimits forget.{u} := forget_preservesColimits
  let : (MorphismProperty.monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape J :=
    sSet_monomorphisms_stable J
  let : PreservesWellOrderContinuousOfShape J forget.{u} := ⟨fun _ _ ↦ inferInstance⟩
  have hm := (h.ofLE (show (fun _ _ f ↦ FreeCofibration f : MorphismProperty DaggerSSet.{u}) ≤
      (MorphismProperty.monomorphisms SSet.{u}).inverseImage forget from
        fun _ _ i hi ↦ (mono_iff_mono_hom i).1 hi.1)).map
  exact (mono_iff_mono_hom f).2
    ((MorphismProperty.monomorphisms SSet).transfiniteCompositionsOfShape_le J _ ⟨hm⟩)

private theorem transfinite_map_mono {J : Type u} [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (h : MorphismProperty.TransfiniteCompositionOfShape
      (fun _ _ f ↦ FreeCofibration f) J f) {a b : J} (g : a ⟶ b) : Mono (h.F.map g) := by
  have he : h.F.map g ≫ h.incl.app b = h.incl.app a := by
    simpa only [Functor.const_obj_map, Category.comp_id] using h.incl.naturality g
  let : Mono (h.F.map g ≫ h.incl.app b) := by
    rw [he]
    exact mono_of_transfinite (h.ici a)
  exact mono_of_mono (h.F.map g) (h.incl.app b)

private theorem jointly_surjective_hom_app {J : Type u} [Category.{u} J]
    {F : J ⥤ DaggerSSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (n : SimplexCategoryᵒᵖ) (y : c.pt.toSSet.obj n) :
    ∃ j x, (c.ι.app j).hom.app n x = y := by
  let : PreservesColimits forget.{u} := forget_preservesColimits
  let ev : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  let : PreservesColimitsOfShape J ev := evaluation_preservesColimitsOfShape n
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ev (isColimitOfPreserves forget hc)) y

private theorem nonDegenerate_fixed_of_mono {X Y : DaggerSSet.{u}} (f : X ⟶ Y) [Mono f]
    {n : ℕ} {x : X.toSSet _⦋n⦌} {y : Y.toSSet _⦋n⦌}
    (hxy : f.hom.app (op ⦋n⦌) x = y) (hy : y ∈ Y.toSSet.nonDegenerate n)
    (hfix : Y.daggerSimplex y = y) :
    x ∈ X.toSSet.nonDegenerate n ∧ X.daggerSimplex x = x := by
  let : Mono f.hom := (mono_iff_mono_hom f).1 inferInstance
  refine ⟨(SSet.nonDegenerate_iff_of_mono f.hom x).1 (hxy.symm ▸ hy), ?_⟩
  apply (CategoryTheory.mono_iff_injective (f.hom.app (op ⦋n⦌))).1 inferInstance
  exact (f.dagger_comm x).trans ((congrArg Y.daggerSimplex hxy).trans (hfix.trans hxy.symm))

private theorem fixed_nonDegenerate_lifts_bot {J : Type u} [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (h : MorphismProperty.TransfiniteCompositionOfShape
      (fun _ _ f ↦ FreeCofibration f) J f) (n : ℕ) (hn : 0 < n) :
    ∀ j (b : (h.F.obj j).toSSet _⦋n⦌), b ∈ (h.F.obj j).toSSet.nonDegenerate n →
      (h.F.obj j).daggerSimplex b = b →
      ∃ a, (h.F.map (homOfLE bot_le : ⊥ ⟶ j)).hom.app (op ⦋n⦌) a = b := by
  intro j
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    intro b hb hfix
    refine ⟨b, ?_⟩
    change (h.F.map (𝟙 ⊥)).hom.app _ b = b
    rw [h.F.map_id]
    rfl
  | succ j hj ih =>
    intro b hb hfix
    have hi := h.map_mem j hj
    by_cases hnew : b ∈ Set.range
        ((h.F.map (homOfLE (Order.le_succ j))).hom.app (op ⦋n⦌))
    · obtain ⟨a, ha⟩ := hnew
      let : Mono (h.F.map (homOfLE (Order.le_succ j))) := hi.1
      obtain ⟨hand, hafix⟩ := nonDegenerate_fixed_of_mono _ ha hb hfix
      obtain ⟨a₀, ha₀⟩ := ih a hand hafix
      refine ⟨a₀, ?_⟩
      have he : h.F.map (homOfLE bot_le : ⊥ ⟶ Order.succ j) =
          h.F.map (homOfLE bot_le : ⊥ ⟶ j) ≫ h.F.map (homOfLE (Order.le_succ j)) := by
        rw [← h.F.map_comp]
        rfl
      rw [he]
      change (h.F.map (homOfLE (Order.le_succ j))).hom.app _
        ((h.F.map (homOfLE bot_le : ⊥ ⟶ j)).hom.app _ a₀) = b
      rw [ha₀]
      exact ha
    · exact False.elim (hi.2 n hn b hb hnew hfix)
  | isSuccLimit j hj ih =>
    intro b hb hfix
    obtain ⟨a, x, hx⟩ := jointly_surjective_hom_app
      (h.F.isColimitOfIsWellOrderContinuous j hj) (op ⦋n⦌) b
    change (h.F.map (homOfLE a.2.le)).hom.app (op ⦋n⦌) x = b at hx
    let : Mono (h.F.map (homOfLE a.2.le)) := transfinite_map_mono h _
    obtain ⟨hxnd, hxfix⟩ := nonDegenerate_fixed_of_mono _ hx hb hfix
    obtain ⟨a₀, ha₀⟩ := ih a.1 a.2 x hxnd hxfix
    refine ⟨a₀, ?_⟩
    have he : h.F.map (homOfLE bot_le : ⊥ ⟶ j) =
        h.F.map (homOfLE bot_le : ⊥ ⟶ a.1) ≫ h.F.map (homOfLE a.2.le) := by
      rw [← h.F.map_comp]
      rfl
    rw [he]
    change (h.F.map (homOfLE a.2.le)).hom.app _
      ((h.F.map (homOfLE bot_le : ⊥ ⟶ a.1)).hom.app _ a₀) = b
    rw [ha₀]
    exact hx

/-- A well-order-continuous transfinite composite of free cofibrations is free.
Both the well-ordered index and the simplex types lie in the arbitrary universe `u`. -/
theorem FreeCofibration.of_transfiniteCompositionOfShape {J : Type u} [LinearOrder J]
    [SuccOrder J] [OrderBot J] [WellFoundedLT J] {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (h : MorphismProperty.TransfiniteCompositionOfShape
      (fun _ _ f ↦ FreeCofibration f) J f) : FreeCofibration f := by
  refine ⟨mono_of_transfinite h, ?_⟩
  intro n hn y hy hnew hfix
  obtain ⟨j, b, hb⟩ := jointly_surjective_hom_app h.isColimit (op ⦋n⦌) y
  let : Mono (h.incl.app j) := mono_of_transfinite (h.ici j)
  obtain ⟨hbnd, hbfix⟩ := nonDegenerate_fixed_of_mono _ hb hy hfix
  obtain ⟨a₀, ha₀⟩ := fixed_nonDegenerate_lifts_bot h n hn j b hbnd hbfix
  apply hnew
  refine ⟨h.isoBot.hom.hom.app (op ⦋n⦌) a₀, ?_⟩
  have hf : h.isoBot.hom ≫ f = h.incl.app ⊥ := h.isoBot.eq_inv_comp.1 h.fac.symm
  have hc : h.F.map (homOfLE bot_le : ⊥ ⟶ j) ≫ h.incl.app j = h.incl.app ⊥ := by
    simpa only [Functor.const_obj_map, Category.comp_id] using
      h.incl.naturality (homOfLE bot_le : ⊥ ⟶ j)
  calc
    f.hom.app _ (h.isoBot.hom.hom.app _ a₀) = (h.incl.app ⊥).hom.app _ a₀ :=
      congrArg (fun g : h.F.obj ⊥ ⟶ Y ↦ g.hom.app (op ⦋n⦌) a₀) hf
    _ = (h.incl.app j).hom.app _ ((h.F.map (homOfLE bot_le : ⊥ ⟶ j)).hom.app _ a₀) :=
      (congrArg (fun g : h.F.obj ⊥ ⟶ Y ↦ g.hom.app (op ⦋n⦌) a₀) hc).symm
    _ = (h.incl.app j).hom.app _ b := congrArg _ ha₀
    _ = y := hb

/-- The unchanged free-cofibration predicate is stable under transfinite
compositions of any well-ordered shape in the simplex universe. -/
theorem freeCofibration_isStableUnderTransfiniteCompositionOfShape (J : Type u)
    [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (fun _ _ f ↦ FreeCofibration f : MorphismProperty DaggerSSet.{u}) J where
  le _ _ _ h := h.elim FreeCofibration.of_transfiniteCompositionOfShape

end DaggerModels.DaggerSSet
