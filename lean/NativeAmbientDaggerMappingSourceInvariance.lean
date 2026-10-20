import NativeAmbientDaggerCotensorFibrations
import OriginalStrictDaggerMappingSourceInvariance

/-! The EXISTING whole cotensor correspondence proves source weak invariance
for the ORIGINAL AMBIENT mapping objects at ALL native fibrant dagger targets.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectDaggerCotensorRepresentation
open DaggerOriginalFixedObjectStrictDaggerCotensorRepresentation
open DaggerNativeAmbientDaggerCotensorFibrations
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeAmbientDaggerMappingSourceInvariance
noncomputable section

theorem mappingSource_lifting {O : Type u} {K L : SSet.{u}} (j : K ⟶ L)
    {A B : FixedDaggerCategory O} (i : A ⟶ B) (D : FixedDaggerCategory O)
    [HasLiftingProperty i (daggerCotensorPre j D)] :
    HasLiftingProperty j (eHomWhiskerRight SSet i D) := by
  constructor
  intro f g sq
  let sq' : CommSq (cotensorHomEquiv A D L g) i (daggerCotensorPre j D)
      (cotensorHomEquiv B D K f) := by
    constructor
    rw [← cotensorHomEquiv_parameter, ← ambientCotensorHomEquiv_source]
    exact congrArg (cotensorHomEquiv A D K) sq.w.symm
  let l := (cotensorHomEquiv B D L).symm sq'.lift
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (cotensorHomEquiv B D K).injective
    rw [cotensorHomEquiv_parameter]
    change (cotensorHomEquiv B D L) ((cotensorHomEquiv B D L).symm sq'.lift) ≫ _ = _
    rw [Equiv.apply_symm_apply]
    exact sq'.fac_right
  · apply (cotensorHomEquiv A D L).injective
    rw [ambientCotensorHomEquiv_source]
    change i ≫ (cotensorHomEquiv B D L) ((cotensorHomEquiv B D L).symm sq'.lift) = _
    rw [Equiv.apply_symm_apply]
    exact sq'.fac_left

theorem mappingSource_trivialFibration {O : Type u} {A B : FixedDaggerCategory O}
    (i : A ⟶ B) [Cofibration i] [WeakEquivalence i] (D : FixedDaggerCategory O)
    [IsFibrant D] : trivialFibrations SSet.{u} (eHomWhiskerRight SSet i D) := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  rintro _ _ _ ⟨n⟩
  have : Fibration (daggerCotensorPre (SSet.boundary n).ι D) :=
    restriction_fibration (SSet.boundary n).ι D
  exact mappingSource_lifting (SSet.boundary n).ι i D

def sourceMappingFunctor {O : Type u} (D : FixedDaggerCategory O) :
    (FixedDaggerCategory O)ᵒᵖ ⥤ SSet.{u} where
  obj A := A.unop ⟶[SSet] D
  map i := eHomWhiskerRight SSet i.unop D
  map_id A := eHomWhiskerRight_id SSet A.unop D
  map_comp i j := by
    change eHomWhiskerRight SSet (i ≫ j).unop D = _
    rw [unop_comp, eHomWhiskerRight_comp]

theorem mappingSource_weak {O : Type u} {A B : FixedDaggerCategory O}
    (i : A ⟶ B) [IsCofibrant A] [IsCofibrant B] [WeakEquivalence i]
    (D : FixedDaggerCategory O) [IsFibrant D] :
    WeakEquivalence (eHomWhiskerRight SSet i D) := by
  exact DaggerOriginalContravariantCofibrantBrownChallengeProof.challengeProof
    (FixedDaggerCategory O) SSet (sourceMappingFunctor D) (by
      intro X Y j hj hw
      have : Cofibration j := hj
      have : WeakEquivalence j := hw
      exact ((mem_trivialFibrations_iff _).mp (mappingSource_trivialFibration j D)).2)
    inferInstance inferInstance i inferInstance

end
end DaggerNativeAmbientDaggerMappingSourceInvariance
