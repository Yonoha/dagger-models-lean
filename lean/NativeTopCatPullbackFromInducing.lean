import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Detecting an actual topological pullback with an inducing first leg

The underlying set pullback gives the unique lift. An inducing first leg
makes that lift continuous. This criterion uses the original four maps and
does not infer topological limit preservation from a set bijection alone.
-/
set_option autoImplicit false
open CategoryTheory Limits Topology
universe u
namespace DaggerNativeTopCatPullbackFromInducing
noncomputable section

/-- An inducing first leg upgrades the underlying set pullback to a TopCat pullback. -/
theorem isPullback_of_underlying_isPullback_of_isInducing
    {W X Y Z : TopCat.{u}} {t : W ⟶ X} {l : W ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}
    (hs : IsPullback ((forget TopCat).map t) ((forget TopCat).map l)
      ((forget TopCat).map r) ((forget TopCat).map b))
    (ht : IsInducing t) : IsPullback t l r b := by
  have hw : t ≫ r = l ≫ b := (forget TopCat).map_injective (by
    simpa only [Functor.map_comp] using hs.w)
  obtain ⟨_, hinj, hsurj⟩ := (Types.isPullback_iff _ _ _ _).1 hs
  let data (s : PullbackCone r b) (x : s.pt) :
      ∃ a : W, t a = s.fst x ∧ l a = s.snd x :=
    hsurj _ _ (ConcreteCategory.congr_hom s.condition x)
  let lift (s : PullbackCone r b) : s.pt ⟶ W := TopCat.ofHom
    { toFun := fun x ↦ Classical.choose (data s x)
      continuous_toFun := by
        apply ht.continuous_iff.2
        convert s.fst.hom.continuous using 1
        funext x
        exact (Classical.choose_spec (data s x)).1 }
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw lift ?_ ?_ ?_⟩⟩
  · intro s
    ext x
    exact (Classical.choose_spec (data s x)).1
  · intro s
    ext x
    exact (Classical.choose_spec (data s x)).2
  · intro s m h₁ h₂
    ext x
    apply hinj
    exact ⟨(ConcreteCategory.congr_hom h₁ x).trans
      (Classical.choose_spec (data s x)).1.symm,
      (ConcreteCategory.congr_hom h₂ x).trans
        (Classical.choose_spec (data s x)).2.symm⟩

end
end DaggerNativeTopCatPullbackFromInducing
