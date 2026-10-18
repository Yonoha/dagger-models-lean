import ActualRightConeFinalEdgePushout

/-! The original cone is categorically equivalent to its SAME final edge, with BOTH endpoints fixed.
-/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerOriginalCounitRightCone DaggerNativeJoyalMappingTest
open DaggerActualRightConeFinalEdgeMaps DaggerActualRightConeFinalEdgePushout
universe u
namespace DaggerActualRightConeFinalEdgeWeak
noncomputable section

theorem section_categorical_weak (n : ℕ) : weakCategoricalEquivalences (sectionMap.{u} n) :=
  DaggerNativeOriginalWeakMonoPushout.weak_of_isPushout (quotient_isPushout n)
    (DaggerNativeTwoBeadSpineGeometry.inclusion_categorical_weak n)

theorem projection_categorical_weak (n : ℕ) : weakCategoricalEquivalences (projection.{u} n) :=
  weakCategoricalEquivalences.of_precomp (sectionMap n) (projection n)
    (section_categorical_weak n)
    ((section_projection n).symm ▸ weakCategoricalEquivalences.id_mem (Δ[1] : SSet.{u}))

theorem section_mono (n : ℕ) : Mono (sectionMap.{u} n) :=
  mono_of_mono_fac (section_projection n)

end
end DaggerActualRightConeFinalEdgeWeak
