import OriginalEC2OrdinaryRealizedPushout
import OriginalEC2FreeCellAction
import OriginalEC2RealizedCellEquivariance

/-!
# Equivariance of the literal simplicial EC₂ attaching legs

The existing ordinary skeletal pushout is equipped with the original regular
action on each coproduct and each skeleton. The two attaching legs intertwine
these actions. Realization and an equivariant CW theorem are separate layers.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2NondegenerateFreeOrbit
open DaggerOriginalEC2RealizedCellEquivariance
open DaggerOriginalEC2SkeletalPushout
open DaggerOriginalEC2OrdinaryRealizedPushout
open DaggerOriginalEC2SkeletonAction DaggerOriginalEC2FreeCellAction

universe u

namespace DaggerOriginalEC2EquivariantAttachingLegs

noncomputable section

private abbrev E : SSet.{u} := simplicialEC2.{u}
private abbrev i : ((⊥ : E.{u}.Subcomplex) : SSet.{u}) ⟶ E.{u} :=
  (⊥ : E.{u}.Subcomplex).ι

/-- The `g`-th characteristic leg is the literal Yoneda map of its orbit simplex. -/
theorem characteristicLeg_inclusion (n : ℕ) (g : C2.{u}) :
    Limits.Sigma.ι (fun (_ : C2.{u}) ↦ (Δ[n] : SSet.{u})) g ≫
        characteristicMap.{u} n ≫ (E.{u}.skeleton (n + 1)).ι =
      SSet.yonedaEquiv.symm (orbitMap.{u} n g).val := by
  simp only [characteristicMap, ← Category.assoc]
  erw [Limits.Sigma.ι_reindex_hom (attachingIndexEquiv.{u} n)
    (fun _ ↦ (Δ[n] : SSet.{u})) g]
  erw [SSet.relativeCellComplexOfMono.ιB_b
    (i := i.{u}) (d := n) ((attachingIndexEquiv.{u} n) g)]
  simp only [Category.assoc, stageIso, SSet.Subcomplex.isoOfEq_hom_ι]
  rfl

/-- On each boundary component, the attaching leg is the restricted same
literal Yoneda map, now landing in the preceding skeleton. -/
theorem attachingLeg_inclusion (n : ℕ) (g : C2.{u}) :
    Limits.Sigma.ι (fun (_ : C2.{u}) ↦ (SSet.boundary n : SSet.{u})) g ≫
        attachingMap.{u} n ≫ (E.{u}.skeleton n).ι =
      (SSet.boundary n).ι ≫
        SSet.yonedaEquiv.symm (orbitMap.{u} n g).val := by
  simp only [attachingMap, ← Category.assoc]
  erw [Limits.Sigma.ι_reindex_hom (attachingIndexEquiv.{u} n)
    (fun _ ↦ (SSet.boundary n : SSet.{u})) g]
  erw [SSet.relativeCellComplexOfMono.ιA_t
    (i := i.{u}) (d := n) ((attachingIndexEquiv.{u} n) g)]
  simp only [Category.assoc, stageIso, SSet.Subcomplex.isoOfEq_hom_ι]
  rfl

/-- The characteristic map intertwines regular permutation of cells with
the original action on the next skeleton. -/
theorem characteristicMap_equivariant (n : ℕ) (h : C2.{u}) :
    (freeCellAction (Δ[n] : SSet.{u})).ρ h ≫ characteristicMap.{u} n =
      characteristicMap.{u} n ≫ (skeletonAction.{u} (n + 1)).ρ h := by
  apply Limits.Sigma.hom_ext
  intro g
  apply (cancel_mono (E.{u}.skeleton (n + 1)).ι).1
  calc
    (Limits.Sigma.ι (fun (_ : C2.{u}) ↦ (Δ[n] : SSet.{u})) g ≫
        (freeCellAction (Δ[n] : SSet.{u})).ρ h ≫ characteristicMap.{u} n) ≫
        (E.{u}.skeleton (n + 1)).ι =
      SSet.yonedaEquiv.symm (orbitMap.{u} n (h * g)).val := by
        rw [← Category.assoc, freeCellAction_ι]
        exact characteristicLeg_inclusion n (h * g)
    _ = SSet.yonedaEquiv.symm (orbitMap.{u} n g).val ≫
        (simplicialAction.{u}.ρ h).asHom := by
          rw [SSet.yonedaEquiv_symm_comp, orbitMap_action]
          rfl
    _ = (Limits.Sigma.ι (fun (_ : C2.{u}) ↦ (Δ[n] : SSet.{u})) g ≫
        characteristicMap.{u} n ≫ (skeletonAction.{u} (n + 1)).ρ h) ≫
        (E.{u}.skeleton (n + 1)).ι := by
          have hc : (skeletonAction.{u} (n + 1)).ρ h ≫
              (E.{u}.skeleton (n + 1)).ι =
                (E.{u}.skeleton (n + 1)).ι ≫
                  (simplicialAction.{u}.ρ h).asHom :=
            (skeletonInclusion.{u} (n + 1)).comm h
          simp only [Category.assoc]
          rw [hc]
          simpa only [Category.assoc] using
            congrArg (fun k ↦ k ≫ (simplicialAction.{u}.ρ h).asHom)
              (characteristicLeg_inclusion n g).symm

/-- The boundary attaching map is equivariant for the same regular orbit. -/
theorem attachingMap_equivariant (n : ℕ) (h : C2.{u}) :
    (freeCellAction (SSet.boundary n : SSet.{u})).ρ h ≫ attachingMap.{u} n =
      attachingMap.{u} n ≫ (skeletonAction.{u} n).ρ h := by
  apply Limits.Sigma.hom_ext
  intro g
  apply (cancel_mono (E.{u}.skeleton n).ι).1
  calc
    (Limits.Sigma.ι
        (fun (_ : C2.{u}) ↦ (SSet.boundary n : SSet.{u})) g ≫
        (freeCellAction (SSet.boundary n : SSet.{u})).ρ h ≫ attachingMap.{u} n) ≫
        (E.{u}.skeleton n).ι =
      (SSet.boundary n).ι ≫
        SSet.yonedaEquiv.symm (orbitMap.{u} n (h * g)).val := by
          rw [← Category.assoc, freeCellAction_ι]
          exact attachingLeg_inclusion n (h * g)
    _ = (SSet.boundary n).ι ≫
        SSet.yonedaEquiv.symm (orbitMap.{u} n g).val ≫
          (simplicialAction.{u}.ρ h).asHom := by
            rw [SSet.yonedaEquiv_symm_comp, orbitMap_action]
            rfl
    _ = (Limits.Sigma.ι
        (fun (_ : C2.{u}) ↦ (SSet.boundary n : SSet.{u})) g ≫
        attachingMap.{u} n ≫ (skeletonAction.{u} n).ρ h) ≫
        (E.{u}.skeleton n).ι := by
          have hc : (skeletonAction.{u} n).ρ h ≫ (E.{u}.skeleton n).ι =
              (E.{u}.skeleton n).ι ≫ (simplicialAction.{u}.ρ h).asHom :=
            (skeletonInclusion.{u} n).comm h
          simp only [Category.assoc]
          rw [hc]
          simpa only [Category.assoc] using
            congrArg (fun k ↦ k ≫ (simplicialAction.{u}.ρ h).asHom)
              (attachingLeg_inclusion n g).symm

/-- The characteristic leg as an actual morphism of simplicial `C₂`-actions. -/
def characteristicHom (n : ℕ) :
    freeCellAction (Δ[n] : SSet.{u}) ⟶ skeletonAction.{u} (n + 1) where
  hom := characteristicMap.{u} n
  comm h := characteristicMap_equivariant n h

/-- The boundary leg as an actual morphism of simplicial `C₂`-actions. -/
def attachingHom (n : ℕ) :
    freeCellAction (SSet.boundary n : SSet.{u}) ⟶ skeletonAction.{u} n where
  hom := attachingMap.{u} n
  comm h := attachingMap_equivariant n h

end

end DaggerOriginalEC2EquivariantAttachingLegs
