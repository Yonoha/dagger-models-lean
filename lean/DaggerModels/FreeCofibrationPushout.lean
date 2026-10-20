import DaggerModels.FreeCofibration
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Stability of free cofibrations under pushouts

We prove the pushout closure asserted in Part I, `dj.lem.free-cof`, for the
original free-cofibration predicate. Degreewise pushouts identify no distinct
elements outside the image of the attaching map; degeneration is preserved
by every simplicial map.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels

/-- A pushout of functions identifies no new element of its left summand
with a different element of that summand, even when the attaching map is not injective. -/
theorem pushout_left_injective_off_range {A B C P : Type u}
    {i : A ⟶ B} {f : A ⟶ C} {j : B ⟶ P} {k : C ⟶ P}
    (sq : IsPushout i f j k) {b₁ b₂ : B}
    (hb₁ : b₁ ∉ Set.range i) (he : j b₁ = j b₂) : b₁ = b₂ := by
  classical
  let code : B ⟶ Option B := fun b ↦ if b ∈ Set.range i then none else some b
  let zero : C ⟶ Option B := fun _ ↦ none
  have hcode : i ≫ code = f ≫ zero := by
    funext a
    simp only [types_comp_apply, code, zero, if_pos (Set.mem_range_self a)]
  obtain ⟨d, hd, _⟩ := sq.exists_desc code zero hcode
  have h : code b₁ = code b₂ := by
    calc
      code b₁ = d (j b₁) := (congrFun hd b₁).symm
      _ = d (j b₂) := congrArg d he
      _ = code b₂ := congrFun hd b₂
  by_cases hb₂ : b₂ ∈ Set.range i
  · simp only [code, if_neg hb₁, if_pos hb₂] at h
    cases h
  · exact Option.some.inj (by simpa only [code, if_neg hb₁, if_neg hb₂] using h)

namespace DaggerSSet

/-- A pushout of dagger simplicial sets is a pushout of types in each degree. -/
theorem isPushout_hom_app {A B C P : DaggerSSet.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {j : B ⟶ P} {k : C ⟶ P}
    (sq : IsPushout i f j k) (n : SimplexCategoryᵒᵖ) :
    IsPushout (i.hom.app n) (f.hom.app n) (j.hom.app n) (k.hom.app n) := by
  let : PreservesColimits forget.{u} := forget_preservesColimits
  let ev : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  let : PreservesColimitsOfShape WalkingSpan ev := evaluation_preservesColimitsOfShape n
  exact (sq.map forget).map ev

/-- A pushout of a free cofibration is again free, as in `dj.lem.free-cof`. -/
theorem FreeCofibration.of_isPushout {A B C P : DaggerSSet.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {j : B ⟶ P} {k : C ⟶ P}
    (sq : IsPushout i f j k) (hi : FreeCofibration i) : FreeCofibration k := by
  let : Mono i.hom := (mono_iff_mono_hom i).1 hi.1
  have hk : Mono k.hom := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    exact Types.pushoutCocone_inr_mono_of_isColimit (isPushout_hom_app sq n).isColimit
  refine ⟨(mono_iff_mono_hom k).2 hk, ?_⟩
  intro n hn w hw hnew hfix
  have sqn := isPushout_hom_app sq (op ⦋n⦌)
  obtain ⟨b, hb⟩ | hc := Types.eq_or_eq_of_isPushout sqn w
  · have hbnew : b ∉ Set.range (i.hom.app (op ⦋n⦌)) := by
      rintro ⟨a, ha⟩
      apply hnew
      refine ⟨f.hom.app (op ⦋n⦌) a, ?_⟩
      calc
        k.hom.app _ (f.hom.app _ a) = j.hom.app _ (i.hom.app _ a) :=
          (congrFun sqn.w a).symm
        _ = j.hom.app _ b := congrArg _ ha
        _ = w := hb
    have hbnondeg : b ∈ B.toSSet.nonDegenerate n := by
      rw [SSet.mem_nonDegenerate_iff_notMem_degenerate]
      intro hbdeg
      have hjdeg := SSet.degenerate_app_apply hbdeg j.hom
      rw [hb] at hjdeg
      exact (SSet.mem_nonDegenerate_iff_notMem_degenerate P.toSSet w).1 hw hjdeg
    apply hi.2 n hn b hbnondeg hbnew
    have he : j.hom.app (op ⦋n⦌) (B.daggerSimplex b) = j.hom.app (op ⦋n⦌) b :=
      (j.dagger_comm b).trans ((congrArg P.daggerSimplex hb).trans (hfix.trans hb.symm))
    exact (pushout_left_injective_off_range sqn hbnew he.symm).symm
  · exact False.elim (hnew hc)

end DaggerSSet
end DaggerModels
