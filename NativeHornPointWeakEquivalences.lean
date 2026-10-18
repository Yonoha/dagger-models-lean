import NativeContractibleSimplexParameter
import NativeConnectedHornsAndSimplex

/-! Every actual global point of a positive native horn is a trivial cofibration. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open Simplicial DaggerNativeContractibleSimplexParameter DaggerNativeStandardSimplexContraction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeHornPointWeakEquivalences
noncomputable section

theorem contractible_terminal_weak {K : SSet.{u}} (c : K.Contractible) :
    WeakEquivalence (toUnit K) := by
  have : WeakEquivalence (snd K (𝟙_ SSet.{u})) := projection_weakEquivalence c _
  have h : (ρ_ K).inv ≫ snd K (𝟙_ SSet.{u}) = toUnit K :=
    isTerminalTensorUnit.hom_ext _ _
  rw [← h]
  infer_instance

theorem contractible_global_point_weak {K : SSet.{u}} (c : K.Contractible)
    (a : 𝟙_ SSet.{u} ⟶ K) : WeakEquivalence a := by
  have : WeakEquivalence (toUnit K) := contractible_terminal_weak c
  have h : a ≫ toUnit K = 𝟙 _ := isTerminalTensorUnit.hom_ext _ _
  exact weakEquivalence_of_postcomp_of_fac h

theorem horn_global_point_weak (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u})) : WeakEquivalence a := by
  have ht : trivialCofibrations SSet.{u} (SSet.horn (n + 1) i).ι :=
    (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mp
      (SSet.anodyneExtensions.horn_ι_mem n i)
  have : WeakEquivalence (SSet.horn (n + 1) i).ι :=
    (mem_trivialCofibrations_iff _).mp ht |>.2
  have : WeakEquivalence (a ≫ (SSet.horn (n + 1) i).ι) :=
    contractible_global_point_weak (simplexContractible (n + 1)) _
  exact weakEquivalence_of_postcomp_of_fac
    (rfl : a ≫ (SSet.horn (n + 1) i).ι = a ≫ (SSet.horn (n + 1) i).ι)

theorem horn_global_point_trivialCofibration (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u})) :
    trivialCofibrations SSet.{u} a := by
  have : Mono a := ⟨fun f g _ ↦ isTerminalTensorUnit.hom_ext f g⟩
  have : Cofibration a := (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  exact (mem_trivialCofibrations_iff _).mpr
    ⟨inferInstance, horn_global_point_weak n i a⟩

end
end DaggerNativeHornPointWeakEquivalences
