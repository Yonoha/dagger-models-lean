import NativeRootedSpinePairingCore
import NativeSpineRootPoint
import NativeDualTheoremA

/-! The actual regular parent pairing makes the native generator spine weakly contractible. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerNativeRootedQuiverPairingData DaggerNativeGeneratorSpineSimplices
open DaggerNativeSpineRootSubcomplex DaggerNativeRootedSpinePairingCore DaggerNativeSpineRootPoint
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRootedSpineContractibility
noncomputable section

variable {W : Type u} [Quiver.{u + 1} W]

theorem root_inclusion_weak (D : Data W) : WeakEquivalence (rootComplex D.root).ι := by
  have ht : trivialCofibrations SSet.{u} (rootComplex D.root).ι := by
    rw [← fibrations_llp]
    exact root_inclusion_anodyne D
  exact (mem_trivialCofibrations_iff _).mp ht |>.2

theorem rootComplex_point_weak (r : W) : WeakEquivalence (pointMap (rootComplex r).toSSet) := by
  let e := (rootIsTerminal r).uniqueUpToIso pointIsTerminal
  have he : e.hom = pointMap (rootComplex r).toSSet := pointIsTerminal.hom_ext _ _
  rw [← he]
  infer_instance

theorem spine_point_weak (D : Data W) : WeakEquivalence (pointMap (spine W)) := by
  have := root_inclusion_weak D
  have := rootComplex_point_weak D.root
  have he : (rootComplex D.root).ι ≫ pointMap (spine W) =
      pointMap (rootComplex D.root).toSSet := pointIsTerminal.hom_ext _ _
  exact weakEquivalence_of_precomp_of_fac he

end
end DaggerNativeRootedSpineContractibility
