import OriginalAntiInvolutiveRelativeCellTransport
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Actual orbit-indexed anti-involutive relative cell pushout

Transport the checked ordinary all-cell attachment square along the exact
orbit/tag and reversed-parameter bijections. Degree zero is included, and no
characteristic map is assumed monic. The anti-involutive pushout follows by
reflection of colimits through the actual forgetful functor.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveRelativeCellPushout

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoClosure
open DaggerModels.OriginalAntiInvolutiveRelativeSkeleton
open DaggerModels.OriginalAntiInvolutiveRelativeCellAttachment
open DaggerModels.OriginalAntiInvolutiveRelativeCellReindex
open DaggerModels.OriginalAntiInvolutiveRelativeCellTransport
open DaggerModels.SSetBoundaryCells

noncomputable section

variable {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) (hf : NormalMono f)

local instance : Mono f := (mono_iff_mono_hom f).2 hf.1
local instance : Mono f.hom := hf.1

/-- Each evaluated orbit-indexed square is the actual pushout of types.
It is transported from the ordinary all-cell attachment square by genuine
bijections, with reversal of the true-tag standard-simplex parameter. -/
theorem attachment_app_isPushout (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    letI : Mono f := (mono_iff_mono_hom f).2 hf.1
    letI : Mono f.hom := hf.1
    IsPushout ((attachingMap f hf n).hom.app k)
      ((boundarySumMap f n).hom.app k)
      (((relativeSkeleton f).map (homOfLE (Nat.le_succ n))).hom.app k)
      ((characteristicSum f hf n).hom.app k) := by
  letI : Mono f := (mono_iff_mono_hom f).2 hf.1
  letI : Mono f.hom := hf.1
  let e₁ := (boundaryCellEquiv f hf n k).toIso
  let e₃ := (fullCellEquiv f hf n k).toIso
  apply (SSetBoundaryCells.attachment_app_isPushout f.hom n k).of_iso'
    e₁ (Iso.refl _) e₃ (Iso.refl _)
  · ext p
    exact (attaching_transport f hf n k p).symm
  · ext p
    exact (boundary_transport f hf n k p).symm
  · rfl
  · ext p
    exact (characteristic_transport f hf n k p).symm

/-- Every successor of the genuine relative skeleton is a pushout of free
boundary generators indexed by the actual new-cell reversal orbits. -/
theorem attachment_isPushout (n : ℕ) :
    letI : Mono f := (mono_iff_mono_hom f).2 hf.1
    letI : Mono f.hom := hf.1
    IsPushout (attachingMap f hf n) (boundarySumMap f n)
      ((relativeSkeleton f).map (homOfLE (Nat.le_succ n)))
      (characteristicSum f hf n) := by
  letI : Mono f := (mono_iff_mono_hom f).2 hf.1
  letI : Mono f.hom := hf.1
  let : ReflectsColimits antiForget.{u} := antiForget_reflectsColimits
  let : ReflectsColimitsOfSize.{0, 0} antiForget.{u} :=
    reflectsSmallestColimits_of_reflectsColimits antiForget
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk
      ((relativeSkeleton f).map (homOfLE (Nat.le_succ n)))
      (characteristicSum f hf n) (attachment_commutes f hf n))
  apply isColimitOfReflects antiForget
  refine (isColimitMapCoconePushoutCoconeEquiv antiForget
    (attachment_commutes f hf n)).symm ?_
  apply evaluationJointlyReflectsColimits
  intro k
  have hcomm : (attachingMap f hf n).hom ≫
      ((relativeSkeleton f).map (homOfLE (Nat.le_succ n))).hom =
      (boundarySumMap f n).hom ≫ (characteristicSum f hf n).hom :=
    congrArg (fun g : boundarySource f n ⟶
      (relativeSkeleton f).obj (n + 1) ↦ g.hom)
        (attachment_commutes f hf n)
  exact (isColimitMapCoconePushoutCoconeEquiv
    ((evaluation _ (Type u)).obj k) hcomm).symm
      (attachment_app_isPushout f hf n k).isColimit

end

end DaggerModels.OriginalAntiInvolutiveRelativeCellPushout
