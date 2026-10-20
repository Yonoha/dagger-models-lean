import NativeSignedPathReduction

/-! Every actual native free-groupoid arrow has a unique reduced native path representative. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeSignedPathWords DaggerNativeFreeGroupoidWordLabels
open DaggerNativeSignedPathReduction
universe u
namespace DaggerNativeFreeGroupoidReducedPaths
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

theorem exists_reduced_path {a b : Quiver.Symmetrify V} (p : Quiver.Path a b) :
    ∃ q : Quiver.Path a b,
      FreeGroup.IsReduced (word q) ∧ (quotientMap V).map q = (quotientMap V).map p := by
  classical
  suffices ∀ n, ∀ {a b : Quiver.Symmetrify V} (p : Quiver.Path a b), p.length = n →
      ∃ q : Quiver.Path a b,
        FreeGroup.IsReduced (word q) ∧ (quotientMap V).map q = (quotientMap V).map p from
    this _ p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b p hp
    by_cases hr : FreeGroup.IsReduced (word p)
    · exact ⟨p, hr, rfl⟩
    · obtain ⟨w, hw⟩ : ∃ w, FreeGroup.Red.Step (word p) w := by
        by_contra hn
        apply hr
        apply FreeGroup.IsReduced.of_forall_not_step
        intro w hw
        exact hn ⟨w, hw⟩
      obtain ⟨q, hq, he⟩ := lift_word_step V p w hw
      have hlen := hw.length
      rw [← hq, word_length, word_length, hp] at hlen
      have hlt : q.length < n := by omega
      obtain ⟨r, hred, hqr⟩ := ih q.length hlt q rfl
      exact ⟨r, hred, hqr.trans he⟩

theorem quotientMap_surjective {a b : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) :
    ∃ p : Quiver.Path a b, (quotientMap V).map p = f := by
  exact Quot.inductionOn f (fun p ↦ ⟨p, rfl⟩)

theorem existsUnique_reduced_path {a b : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) :
    ∃! p : Quiver.Path a b, FreeGroup.IsReduced (word p) ∧ (quotientMap V).map p = f := by
  obtain ⟨p, rfl⟩ := quotientMap_surjective V f
  obtain ⟨q, hq, he⟩ := exists_reduced_path V p
  refine ⟨q, ⟨hq, he⟩, ?_⟩
  intro r hr
  exact reduced_paths_equal_of_quotient_eq V r q hr.1 hq (hr.2.trans he.symm)

def reducedPathEquiv (a b : Quiver.Symmetrify V) :
    {p : Quiver.Path a b // FreeGroup.IsReduced (word p)} ≃
      ((quotientMap V).obj a ⟶ (quotientMap V).obj b) :=
  Equiv.ofBijective (fun p ↦ (quotientMap V).map p.val) ⟨by
    intro p q h
    exact Subtype.ext (reduced_paths_equal_of_quotient_eq V p.val q.val p.property q.property h),
    by
      intro f
      obtain ⟨p, hp, _⟩ := existsUnique_reduced_path V f
      exact ⟨⟨p, hp.1⟩, hp.2⟩⟩

end
end DaggerNativeFreeGroupoidReducedPaths
