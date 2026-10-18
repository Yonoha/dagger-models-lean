import ActualGeneralRightConeRigidificationWeak
import ActualGeneralRightMappingQKanBridge

/-! The ORIGINAL right mapping maps are weak iff the ORIGINAL rigidification Hom maps are weak.
Both source and target range over ALL original quasi-categories, with BOTH endpoints retained.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerActualGeneralRightConeRigidificationLeg
open DaggerActualGeneralRightConeRigidificationComparison
open DaggerActualGeneralRightConeRigidificationWeak DaggerActualGeneralRightMappingQKanBridge
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualGeneralIntrinsicLocalComparison
noncomputable section

theorem mapping_weak_iff_hom_weak {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (DaggerActualGeneralRightConeMapping.map f a b) ↔
      WeakEquivalence (homMap X a b f) := by
  let A := realization.map (DaggerActualGeneralRightConeMapping.map f a b)
  let E := toRealization X a b
  let F := toRealization Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)
  let H := homMap X a b f
  have : WeakEquivalence E := toRealization_weak X a b
  have : WeakEquivalence F := toRealization_weak Y _ _
  have hs : A ≫ F = E ≫ H := toRealization_naturality X a b f
  constructor
  · intro h
    have : WeakEquivalence A := (realization_map_weak_iff f a b).mpr h
    have hc : WeakEquivalence (A ≫ F) := inferInstance
    have : WeakEquivalence (E ≫ H) := hs ▸ hc
    exact weakEquivalence_of_precomp E H
  · intro h
    have : WeakEquivalence H := h
    have hc : WeakEquivalence (E ≫ H) := inferInstance
    have : WeakEquivalence (A ≫ F) := hs.symm ▸ hc
    have hA : WeakEquivalence A := weakEquivalence_of_postcomp A F
    exact (realization_map_weak_iff f a b).mp hA

end
end DaggerActualGeneralIntrinsicLocalComparison
