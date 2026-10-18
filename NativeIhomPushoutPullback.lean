import NativeCoreMappingWeakRecognition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Actual internal Hom sends an original pushout to a pullback, retaining all four maps. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed
universe u
namespace DaggerNativeIhomPushoutPullback
noncomputable section

def tensorPushout {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (K : SSet.{u}) :
    IsPushout (i ▷ K) (a ▷ K) (b ▷ K) (j ▷ K) := h.map (tensorRight K)

def glue {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (Z K : SSet.{u})
    (x : K ⟶ (ihom B).obj Z) (y : K ⟶ (ihom C).obj Z)
    (w : x ≫ (MonoidalClosed.pre i).app Z = y ≫ (MonoidalClosed.pre a).app Z) :
    K ⟶ (ihom D).obj Z :=
  curry (PushoutCocone.IsColimit.desc (tensorPushout h K).isColimit
    (uncurry x) (uncurry y) (by
    simpa only [uncurry_pre_app] using congrArg MonoidalClosed.uncurry w))

theorem glue_left {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (Z K : SSet.{u})
    (x : K ⟶ (ihom B).obj Z) (y : K ⟶ (ihom C).obj Z)
    (w : x ≫ (MonoidalClosed.pre i).app Z = y ≫ (MonoidalClosed.pre a).app Z) :
    glue h Z K x y w ≫ (MonoidalClosed.pre b).app Z = x := by
  apply uncurry_injective
  simp only [uncurry_pre_app, glue, uncurry_curry]
  exact PushoutCocone.IsColimit.inl_desc (tensorPushout h K).isColimit _ _ _

theorem glue_right {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (Z K : SSet.{u})
    (x : K ⟶ (ihom B).obj Z) (y : K ⟶ (ihom C).obj Z)
    (w : x ≫ (MonoidalClosed.pre i).app Z = y ≫ (MonoidalClosed.pre a).app Z) :
    glue h Z K x y w ≫ (MonoidalClosed.pre j).app Z = y := by
  apply uncurry_injective
  simp only [uncurry_pre_app, glue, uncurry_curry]
  exact PushoutCocone.IsColimit.inr_desc (tensorPushout h K).isColimit _ _ _

theorem hom_ext {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (Z K : SSet.{u})
    (x y : K ⟶ (ihom D).obj Z)
    (hl : x ≫ (MonoidalClosed.pre b).app Z = y ≫ (MonoidalClosed.pre b).app Z)
    (hr : x ≫ (MonoidalClosed.pre j).app Z = y ≫ (MonoidalClosed.pre j).app Z) : x = y := by
  apply uncurry_injective
  apply PushoutCocone.IsColimit.hom_ext (tensorPushout h K).isColimit
  · simpa only [uncurry_pre_app] using congrArg MonoidalClosed.uncurry hl
  · simpa only [uncurry_pre_app] using congrArg MonoidalClosed.uncurry hr

def isPullback {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) (Z : SSet.{u}) :
    IsPullback ((MonoidalClosed.pre b).app Z) ((MonoidalClosed.pre j).app Z)
      ((MonoidalClosed.pre i).app Z) ((MonoidalClosed.pre a).app Z) := by
  have w : (MonoidalClosed.pre b).app Z ≫ (MonoidalClosed.pre i).app Z =
      (MonoidalClosed.pre j).app Z ≫ (MonoidalClosed.pre a).app Z := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, ← NatTrans.comp_app,
      ← MonoidalClosed.pre_map, h.w]
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk ((MonoidalClosed.pre b).app Z) ((MonoidalClosed.pre j).app Z) w)
  apply PullbackCone.IsLimit.mk w
    (fun s ↦ glue h Z s.pt s.fst s.snd s.condition)
  · exact fun s ↦ glue_left h Z s.pt s.fst s.snd s.condition
  · exact fun s ↦ glue_right h Z s.pt s.fst s.snd s.condition
  · intro s m hm hn
    apply hom_ext h Z s.pt
    · rw [hm, glue_left]
    · rw [hn, glue_right]

end
end DaggerNativeIhomPushoutPullback
