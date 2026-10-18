import NativeAmbientDaggerMappingSourceInvariance

/-! The WHOLE ORIGINAL ambient enriched mapping object is Kan
for EVERY cofibrant source and EVERY native fibrant dagger target.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectDaggerCotensorRepresentation
open DaggerNativeAmbientDaggerCotensorFibrations DaggerNativeAmbientDaggerMappingSourceInvariance
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeAmbientDaggerMappingKan
noncomputable section

theorem mappingSource_fibration {O : Type u} {A B : FixedDaggerCategory O}
    (i : A ⟶ B) [Cofibration i] (D : FixedDaggerCategory O) [IsFibrant D] :
    Fibration (eHomWhiskerRight SSet i D) := by
  rw [fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]
  intro K L j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨a⟩⟩ := hj
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp
    (restriction_trivialFibration (SSet.horn (n + 1) a).ι
      (SSet.anodyneExtensions.horn_ι_mem n a) D)
  have : Fibration (daggerCotensorPre (SSet.horn (n + 1) a).ι D) := hf
  have : WeakEquivalence (daggerCotensorPre (SSet.horn (n + 1) a).ι D) := hw
  exact mappingSource_lifting (SSet.horn (n + 1) a).ι i D

def initialMappingIsTerminal {O : Type u} (D : FixedDaggerCategory O) :
    IsTerminal ((⊥_ (FixedDaggerCategory O)) ⟶[SSet.{u}] D) :=
  IsTerminal.ofUniqueHom
    (fun K ↦ (cotensorHomEquiv (⊥_ (FixedDaggerCategory O)) D K).symm
      (initial.to (daggerCotensor K D))) (by
        intro K F
        apply (cotensorHomEquiv (⊥_ (FixedDaggerCategory O)) D K).injective
        rw [Equiv.apply_symm_apply]
        exact initialIsInitial.hom_ext _ _)

theorem mapping_kan {O : Type u} (A D : FixedDaggerCategory O)
    [IsCofibrant A] [IsFibrant D] : (A ⟶[SSet.{u}] D).KanComplex := by
  have : Cofibration (initial.to A) := (isCofibrant_iff A).mp inferInstance
  have : Fibration (eHomWhiskerRight SSet (initial.to A) D) :=
    mappingSource_fibration (initial.to A) D
  exact (isFibrant_iff_of_isTerminal (eHomWhiskerRight SSet (initial.to A) D)
    (initialMappingIsTerminal D)).mpr inferInstance

end
end DaggerNativeAmbientDaggerMappingKan
