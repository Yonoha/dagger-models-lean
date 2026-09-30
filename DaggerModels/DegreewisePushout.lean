import DaggerModels.FreeCofibration
import DaggerModels.ForgetfulReflection
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# A degreewise criterion for dagger pushouts

For the actual cell-attachment squares in Part I, `dj.lem.free-cof`, we use
the set-theoretic characterization of a pushout along a monomorphism.
The attaching map itself need not be monic. The hypotheses describe the
intersection, coverage, and uniqueness of the newly attached simplices.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.DaggerSSet

/-- Degreewise pushouts give a pushout in the original dagger category. -/
theorem isPushout_of_hom_app {A B C P : DaggerSSet.{u}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ P} {b : C ⟶ P}
    (w : t ≫ r = l ≫ b)
    (h : ∀ n : SimplexCategoryᵒᵖ,
      IsPushout (t.hom.app n) (l.hom.app n) (r.hom.app n) (b.hom.app n)) :
    IsPushout t l r b := by
  let : ReflectsColimits forget.{u} := forget_reflectsColimits
  let : ReflectsColimitsOfSize.{0, 0} forget.{u} :=
    reflectsSmallestColimits_of_reflectsColimits forget
  apply IsPushout.of_map forget w
  have hw : t.hom ≫ r.hom = l.hom ≫ b.hom := congrArg Hom.hom w
  apply IsPushout.of_isColimit (c := PushoutCocone.mk r.hom b.hom hw)
  apply evaluationJointlyReflectsColimits
  intro n
  exact (isColimitMapCoconePushoutCoconeEquiv
    ((evaluation _ (Type u)).obj n) hw).symm (h n).isColimit

/-- A monic square is a pushout if it has the stated degreewise intersection,
coverage, and injectivity on the complement of the boundary image. -/
theorem isPushout_of_degreewise_complement {A B C P : DaggerSSet.{u}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ P} {b : C ⟶ P}
    [Mono l] [Mono r] (w : t ≫ r = l ≫ b)
    (hpre : ∀ n (x : C.toSSet.obj n),
      b.hom.app n x ∈ Set.range (r.hom.app n) → x ∈ Set.range (l.hom.app n))
    (hcover : ∀ n (x : P.toSSet.obj n),
      x ∈ Set.range (r.hom.app n) ∨ x ∈ Set.range (b.hom.app n))
    (hinj : ∀ n (x y : C.toSSet.obj n),
      x ∉ Set.range (l.hom.app n) → y ∉ Set.range (l.hom.app n) →
      b.hom.app n x = b.hom.app n y → x = y) : IsPushout t l r b := by
  have hl : Mono l.hom := (mono_iff_mono_hom l).1 inferInstance
  have hr : Mono r.hom := (mono_iff_mono_hom r).1 inferInstance
  apply isPushout_of_hom_app w
  intro n
  have hl' : Function.Injective (l.hom.app n) :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app l.hom).1 hl n)
  let : Mono (r.hom.app n) := (NatTrans.mono_iff_mono_app r.hom).1 hr n
  have hr' : Function.Injective (r.hom.app n) := (mono_iff_injective _).1 inferInstance
  have wn : t.hom.app n ≫ r.hom.app n = l.hom.app n ≫ b.hom.app n :=
    NatTrans.congr_app (congrArg Hom.hom w) n
  apply Types.isPushout_of_isPullback_of_mono'
  · rw [Types.isPullback_iff]
    refine ⟨wn, fun x y hxy ↦ hl' hxy.2, ?_⟩
    intro x y hxy
    obtain ⟨a, ha⟩ := hpre n y ⟨x, hxy⟩
    refine ⟨a, hr' ?_, ha⟩
    exact (congrFun wn a).trans ((congrArg (b.hom.app n) ha).trans hxy.symm)
  · exact Set.eq_univ_of_forall (hcover n)
  · exact hinj n

end DaggerModels.DaggerSSet
