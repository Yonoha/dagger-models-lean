import OriginalTaggedReversePresheafInclusion
import OriginalTaggedReverseFreeCompletion
import DaggerModels.FreeCofibration

/-!
# Unconditional normality comparison for the actual tagged restriction

This is the point-set part of `pointset.thm.cofibrations`. The normal-mono
predicate is the explicit free-action condition on the actual anti-involutive
category. No DCH model structure or DCH cofibration characterization is
assumed here.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite
open DaggerModels
open DaggerModels.OriginalTaggedReversePresheafInclusion

universe u

namespace DaggerModels.OriginalTaggedNormalModelInputs

noncomputable section

private theorem restrictedHom_app {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (q : SimplexCategoryᵒᵖ) (x : X.toSSet.obj q) :
    ((presheafRoute.{u}.map f).hom.app q) x = f.hom.app q x := by
  have h := congrFun (NatTrans.congr_app
    (congrArg AntiInvolutiveSSet.Hom.hom (comparisonIso.{u}.hom.naturality f)) q) x
  simpa only [NatTrans.comp_app, comparisonComponent_hom_app] using h

private theorem restricted_mono_iff {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    Mono (presheafRoute.{u}.map f).hom ↔ Mono f.hom := by
  rw [NatTrans.mono_iff_mono_app, NatTrans.mono_iff_mono_app]
  constructor
  · intro h q
    rw [mono_iff_injective]
    intro x y hxy
    apply (mono_iff_injective _).1 (h q)
    simpa only [restrictedHom_app] using hxy
  · intro h q
    rw [mono_iff_injective]
    intro x y hxy
    apply (mono_iff_injective _).1 (h q)
    simpa only [restrictedHom_app] using hxy

private theorem restricted_nondegenerate_iff (X : DaggerSSet.{u})
    (n : ℕ) (x : X.toSSet _⦋n⦌) :
    x ∈ (presheafRoute.{u}.obj X).toSSet.nonDegenerate n ↔
      x ∈ X.toSSet.nonDegenerate n := by
  let e := OriginalTaggedReverseFreeCompletion.antiForget.{u}.mapIso
    (comparisonComponent X)
  have h := SSet.nonDegenerate_iff_of_isIso e.hom x
  simpa only [comparisonComponent_hom_app] using h.symm

/-- On an actual dagger map, the tagged normality condition is precisely the
original free-cofibration condition together with surjectivity on vertices. -/
theorem restricted_normalMono_iff_freeCofibration_and_vertex_surjective
    {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    AntiInvolutiveSSet.NormalMono (presheafRoute.{u}.map f) ↔
      DaggerSSet.FreeCofibration f ∧
        Function.Surjective (f.hom.app (op ⦋0⦌)) := by
  constructor
  · intro h
    have hmono : Mono f.hom := (restricted_mono_iff f).1 h.1
    have hfree : DaggerSSet.FreeCofibration f := by
      refine ⟨(DaggerSSet.mono_iff_mono_hom f).2 hmono, ?_⟩
      intro n hn x hx hnew hfixed
      have hanti := h.2 n x ((restricted_nondegenerate_iff Y n x).2 hx)
        (by simpa only [restrictedHom_app] using hnew)
      apply hanti
      rw [restrictedDagger]
      exact hfixed
    have hsurj : Function.Surjective (f.hom.app (op ⦋0⦌)) := by
      intro y
      by_contra hmissing
      have hnd : y ∈ (presheafRoute.{u}.obj Y).toSSet.nonDegenerate 0 := by
        simp [SSet.nondegenerate_zero]
      have hfixed : (presheafRoute.{u}.obj Y).daggerSimplex y = y := by
        rw [restrictedDagger]
        exact Y.dagger_vertex y
      exact h.2 0 y hnd hmissing hfixed
    exact ⟨hfree, hsurj⟩
  · rintro ⟨hfree, hsurj⟩
    refine ⟨(restricted_mono_iff f).2
      ((DaggerSSet.mono_iff_mono_hom f).1 hfree.1), ?_⟩
    intro n x hx hnew
    cases n with
    | zero =>
        exfalso
        exact hnew (hsurj x)
    | succ k =>
        have hpos : 0 < k + 1 := Nat.zero_lt_succ k
        have hnot : Y.daggerSimplex x ≠ x := hfree.2 (k + 1) hpos x
          ((restricted_nondegenerate_iff Y (k + 1) x).1 hx)
          (by simpa only [restrictedHom_app] using hnew)
        rw [restrictedDagger]
        exact hnot

end

end DaggerModels.OriginalTaggedNormalModelInputs
