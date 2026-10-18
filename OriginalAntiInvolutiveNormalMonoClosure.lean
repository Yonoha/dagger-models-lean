import OriginalTaggedNormalModelInputs
import OriginalTaggedReverseFreeCompletion
import DaggerModels.FreeCofibration
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Closure of the explicit anti-involutive normal monomorphisms

These are direct point-set closure results for the actual DCH-style
free-action predicate in every degree, including vertices. They do not
construct or assume a DCH model category.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite
open DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion

universe u

namespace DaggerModels.OriginalAntiInvolutiveNormalMonoClosure

noncomputable section

private instance : antiForget.{u}.Faithful where
  map_injective h := AntiInvolutiveSSet.Hom.ext h

/-- Monicity is detected on the entire underlying simplicial set. -/
theorem mono_iff_mono_hom {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom := by
  let : antiForget.{u}.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction freeAntiAdjunction
  exact (antiForget.mono_map_iff_mono f).symm

/-- Identity maps have no new nondegenerate simplices in any degree. -/
theorem normalMono_id (X : AntiInvolutiveSSet.{u}) :
    AntiInvolutiveSSet.NormalMono (𝟙 X) := by
  refine ⟨(mono_iff_mono_hom (𝟙 X)).1 inferInstance, ?_⟩
  intro n x _ hnew
  exact False.elim (hnew ⟨x, rfl⟩)

/-- The explicit normality predicate is stable under composition. -/
theorem NormalMono.comp {X Y Z : AntiInvolutiveSSet.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : AntiInvolutiveSSet.NormalMono f)
    (hg : AntiInvolutiveSSet.NormalMono g) :
    AntiInvolutiveSSet.NormalMono (f ≫ g) := by
  let : Mono f.hom := hf.1
  let : Mono g.hom := hg.1
  letI : Mono f := (mono_iff_mono_hom f).2 hf.1
  letI : Mono g := (mono_iff_mono_hom g).2 hg.1
  refine ⟨(mono_iff_mono_hom (f ≫ g)).1 inferInstance, ?_⟩
  intro n z hz hnew
  by_cases hgz : z ∈ Set.range (g.hom.app (op ⦋n⦌))
  · obtain ⟨y, rfl⟩ := hgz
    have hy : y ∈ Y.toSSet.nonDegenerate n :=
      (SSet.nonDegenerate_iff_of_mono g.hom y).1 hz
    have hynew : y ∉ Set.range (f.hom.app (op ⦋n⦌)) := by
      rintro ⟨x, rfl⟩
      exact hnew ⟨x, rfl⟩
    intro hfix
    apply hf.2 n y hy hynew
    apply (CategoryTheory.mono_iff_injective (g.hom.app (op ⦋n⦌))).1 inferInstance
    exact (g.dagger_comm y).trans hfix
  · exact hg.2 n z hz hgz

/-- A retract of an actual normal monomorphism is normal in every degree. -/
theorem NormalMono.of_retract {X Y Z W : AntiInvolutiveSSet.{u}}
    {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
    (hg : AntiInvolutiveSSet.NormalMono g) :
    AntiInvolutiveSSet.NormalMono f := by
  have hgMono : Mono g := (mono_iff_mono_hom g).2 hg.1
  have hfMono : Mono f := MorphismProperty.of_retract
    (P := MorphismProperty.monomorphisms AntiInvolutiveSSet.{u}) h hgMono
  let : Mono h.i.right.hom := (mono_iff_mono_hom h.i.right).1 inferInstance
  refine ⟨(mono_iff_mono_hom f).1 hfMono, ?_⟩
  intro n y hy hnew hfix
  have hiy : h.i.right.hom.app (op ⦋n⦌) y ∈ W.toSSet.nonDegenerate n :=
    (SSet.nonDegenerate_iff_of_mono h.i.right.hom y).2 hy
  have hiynew : h.i.right.hom.app (op ⦋n⦌) y ∉
      Set.range (g.hom.app (op ⦋n⦌)) := by
    rintro ⟨z, hz⟩
    apply hnew
    refine ⟨h.r.left.hom.app (op ⦋n⦌) z, ?_⟩
    calc
      f.hom.app _ (h.r.left.hom.app _ z) = h.r.right.hom.app _ (g.hom.app _ z) :=
        congrArg (fun k : Z ⟶ Y ↦ k.hom.app (op ⦋n⦌) z) h.r_w
      _ = h.r.right.hom.app _ (h.i.right.hom.app _ y) := congrArg _ hz
      _ = y := congrArg (fun k : Y ⟶ Y ↦ k.hom.app (op ⦋n⦌) y) h.retract_right
  apply hg.2 n _ hiy hiynew
  exact (h.i.right.dagger_comm y).symm.trans (congrArg _ hfix)

end

end DaggerModels.OriginalAntiInvolutiveNormalMonoClosure
