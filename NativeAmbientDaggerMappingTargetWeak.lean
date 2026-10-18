import NativeAmbientDaggerMappingTargetLifting
import OriginalFibrantBrownPreservationChallengeProof

/-! Brown's EXISTING native theorem gives target weak invariance of the SAME original
ambient enriched mapping space, for ANY cofibrant source and ALL fibrant dagger targets.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeAmbientDaggerMappingTargetLifting
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeAmbientDaggerMappingTargetWeak
noncomputable section

def targetMappingFunctor {O : Type u} (A : FixedDaggerCategory O) :
    FixedDaggerCategory O ⥤ SSet.{u} where
  obj D := A ⟶[SSet] D
  map p := eHomWhiskerLeft SSet A p
  map_id D := eHomWhiskerLeft_id SSet A D
  map_comp p q := eHomWhiskerLeft_comp SSet A p q

theorem mappingTarget_weak {O : Type u} (A : FixedDaggerCategory O) [IsCofibrant A]
    {C D : FixedDaggerCategory O} (p : C ⟶ D)
    [IsFibrant C] [IsFibrant D] [WeakEquivalence p] :
    WeakEquivalence (eHomWhiskerLeft SSet A p) := by
  exact DaggerOriginalFibrantBrownPreservationChallengeProof.challengeProof
    (FixedDaggerCategory O) SSet (targetMappingFunctor A) (by
      intro X Y f hf hw
      have : Fibration f := hf
      have : WeakEquivalence f := hw
      exact ((mem_trivialFibrations_iff _).mp (mappingTarget_trivialFibration A f)).2)
    inferInstance inferInstance p inferInstance

end
end DaggerNativeAmbientDaggerMappingTargetWeak
