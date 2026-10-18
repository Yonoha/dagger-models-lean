import OriginalEC2SkeletalPushout
import OriginalEC2SkeletonAction
import TopCatModelCategory.TopCat.Adj

/-!
# Literal ordinary and realized stages of the actual `EC₂` attachment

The stage maps are the underlying maps of the already constructed equivariant
skeletal transitions. Realization preserves these actual pushout squares.
Equivariance of the attaching legs and model cofibrancy remain separate.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2SkeletalPushout DaggerOriginalEC2SkeletonAction

universe u

namespace DaggerOriginalEC2OrdinaryRealizedPushout

noncomputable section

private abbrev E : SSet.{u} := simplicialEC2.{u}
private abbrev i : ((⊥ : E.{u}.Subcomplex) : SSet.{u}) ⟶ E.{u} :=
  (⊥ : E.{u}.Subcomplex).ι

/-- Identify each retained relative stage with the literal ordinary skeleton. -/
def stageIso (n : ℕ) :
    (SSet.skeletonOfMono i.{u} n : SSet.{u}) ≅ (E.{u}.skeleton n : SSet.{u}) :=
  SSet.Subcomplex.isoOfEq (bottomSkeleton.{u} n)

/-- The actual attaching map, with its ordinary skeletal target. -/
def attachingMap (n : ℕ) :
    (∐ (fun (_ : C2.{u}) ↦ (SSet.boundary n : SSet.{u}))) ⟶
      (E.{u}.skeleton n : SSet.{u}) :=
  (boundaryCoproductIso.{u} n).hom ≫ SSet.relativeCellComplexOfMono.t i.{u} n ≫
    (stageIso.{u} n).hom

/-- The actual characteristic maps, with the next ordinary skeletal target. -/
def characteristicMap (n : ℕ) :
    (∐ (fun (_ : C2.{u}) ↦ (Δ[n] : SSet.{u}))) ⟶
      (E.{u}.skeleton (n + 1) : SSet.{u}) :=
  (simplexCoproductIso.{u} n).hom ≫ SSet.relativeCellComplexOfMono.b i.{u} n ≫
    (stageIso.{u} (n + 1)).hom

/-- The transition is exactly the already bundled equivariant inclusion. -/
def stageMap (n : ℕ) :
    (E.{u}.skeleton n : SSet.{u}) ⟶ (E.{u}.skeleton (n + 1) : SSet.{u}) :=
  (skeletonTransition.{u} n).hom

/-- The actual ordinary skeleton is attached by the boundary coproduct square. -/
theorem ordinarySkeletalPushout (n : ℕ) :
    IsPushout (attachingMap.{u} n) (boundaryMap.{u} n)
      (stageMap.{u} n) (characteristicMap.{u} n) := by
  apply (skeletalPushout.{u} n).of_iso (Iso.refl _) (stageIso.{u} n)
    (Iso.refl _) (stageIso.{u} (n + 1))
  · simp [attachingMap]
  · simp
  · apply (cancel_mono (E.{u}.skeleton (n + 1)).ι).1
    simp only [Category.assoc]
    change SSet.relativeCellComplexOfMono.r i.{u} n ≫
        (stageIso.{u} (n + 1)).hom ≫ (E.{u}.skeleton (n + 1)).ι =
      (stageIso.{u} n).hom ≫ (stageMap.{u} n ≫ (E.{u}.skeleton (n + 1)).ι)
    simp only [stageIso, SSet.Subcomplex.isoOfEq_hom_ι, stageMap,
      skeletonTransition, SSet.relativeCellComplexOfMono.r,
      SSet.Subcomplex.homOfLE_ι]
  · simp [characteristicMap]

/-- The actual geometric realization preserves the literal skeletal square. -/
theorem realizedSkeletalPushout (n : ℕ) :
    IsPushout (SSet.toTop.{u}.map (attachingMap.{u} n))
      (SSet.toTop.{u}.map (boundaryMap.{u} n))
      (SSet.toTop.{u}.map (stageMap.{u} n))
      (SSet.toTop.{u}.map (characteristicMap.{u} n)) :=
  (ordinarySkeletalPushout.{u} n).map SSet.toTop.{u}

end

end DaggerOriginalEC2OrdinaryRealizedPushout
