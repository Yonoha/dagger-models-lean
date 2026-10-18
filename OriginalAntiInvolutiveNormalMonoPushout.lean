import OriginalAntiInvolutiveNormalMonoClosure
import DaggerModels.FreeCofibrationPushout
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Pushout stability of the explicit anti-involutive normal monomorphisms

The forgetful functor computes colimits degreewise, and a pushout of a normal
monomorphism leaves each new nondegenerate simplex in the unattached summand.
This includes degree zero and does not assume a DCH model structure.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Functor Simplicial Opposite
open DaggerModels
open DaggerModels.OriginalTaggedReverseSimplex TaggedReverseSimplex
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoClosure

universe u

namespace DaggerModels.OriginalAntiInvolutiveNormalMonoPushout

noncomputable section

/-- Ordinary restriction of anti-involutive presheaves preserves all colimits. -/
theorem antiForget_preservesColimits : PreservesColimits antiForget.{u} := by
  letI : PreservesColimits AntiInvolutiveSSet.toPresheaf.{u} :=
    Adjunction.leftAdjoint_preservesColimits antiInvolutiveEquivalence.toAdjunction
  letI : PreservesColimits
      ((whiskeringLeft _ _ (Type u)).obj
        simplexInclusion.op) :=
    whiskeringLeft_preservesColimit simplexInclusion.op
  exact Limits.preservesColimits_of_natIso
    OriginalTaggedReverseFreeCompletion.extensionRestrictionIso

/-- An anti-involutive pushout is a pushout of types in each simplicial degree. -/
theorem isPushout_hom_app {A B C P : AntiInvolutiveSSet.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {j : B ⟶ P} {k : C ⟶ P}
    (sq : IsPushout i f j k) (n : SimplexCategoryᵒᵖ) :
    IsPushout (i.hom.app n) (f.hom.app n) (j.hom.app n) (k.hom.app n) := by
  let : PreservesColimits antiForget.{u} := antiForget_preservesColimits
  let ev : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  let : PreservesColimitsOfShape WalkingSpan ev := evaluation_preservesColimitsOfShape n
  exact (sq.map antiForget).map ev

/-- Pushout along any map preserves free dagger action on all new simplices. -/
theorem NormalMono.of_isPushout {A B C P : AntiInvolutiveSSet.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {j : B ⟶ P} {k : C ⟶ P}
    (sq : IsPushout i f j k) (hi : AntiInvolutiveSSet.NormalMono i) :
    AntiInvolutiveSSet.NormalMono k := by
  let : Mono i.hom := hi.1
  have hk : Mono k.hom := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    exact Types.pushoutCocone_inr_mono_of_isColimit (isPushout_hom_app sq n).isColimit
  refine ⟨hk, ?_⟩
  intro n w hw hnew hfix
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
    apply hi.2 n b hbnondeg hbnew
    have he : j.hom.app (op ⦋n⦌) (B.daggerSimplex b) = j.hom.app (op ⦋n⦌) b :=
      (j.dagger_comm b).trans ((congrArg P.daggerSimplex hb).trans (hfix.trans hb.symm))
    exact (pushout_left_injective_off_range sqn hbnew he.symm).symm
  · exact False.elim (hnew hc)

end

end DaggerModels.OriginalAntiInvolutiveNormalMonoPushout
