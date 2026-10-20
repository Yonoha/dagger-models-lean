import OriginalStrictDaggerMappingSourceInvariance

/-!
# Kan mapping objects for every actual cofibrant strict dagger source

The original cotensor sends an anodyne parameter to a trivial fibration on all
original Hom objects. Lifting against a cofibration therefore proves native
mapping fibrations. The mapping object of the native initial source is terminal
by the same full cotensor equivalence. This proves Kan for every cofibrant source.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalFixedObjectStrictDaggerCotensorRepresentation
open DaggerOriginalStrictDaggerMappingSourceInvariance
open DaggerOriginalFixedObjectGroupoidInterval DaggerOriginalSimplicialCotensorRestriction
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
  DaggerOriginalFixedObjectCofibrations DaggerOriginalFixedObjectStrictDaggerModel
universe u
namespace DaggerOriginalStrictDaggerMappingCofibrantKan
noncomputable section

/-- Anodyne parameter restriction gives an actual strict trivial fibration on all Hom. -/
theorem strictRestriction_trivialFibration {O : Type u} {K L : SSet.{u}} (j : K ⟶ L)
    (hj : SSet.anodyneExtensions j) (D : FixedStrictDaggerGroupoids O) :
    trivialFibrations (FixedStrictDaggerGroupoids O)
      (((strictDaggerCotensorBifunctor O).map j.op).app D) := by
  rw [mem_trivialFibrations_iff,
    DaggerOriginalFixedObjectGroupoidClasses.strictDagger_fibration_iff,
    DaggerOriginalFixedObjectGroupoidClasses.strictDagger_weakEquivalence_iff]
  constructor
  · intro x y
    have : (D.obj.underlying.enriched.Hom x y).KanComplex :=
      fixedStrictHom_kan ⟨D.obj.underlying, D.property⟩ x y
    exact ((mem_trivialFibrations_iff _).1
      (pre_trivialFibration j hj (D.obj.underlying.enriched.Hom x y))).1
  · intro x y
    have : (D.obj.underlying.enriched.Hom x y).KanComplex :=
      fixedStrictHom_kan ⟨D.obj.underlying, D.property⟩ x y
    exact ((mem_trivialFibrations_iff _).1
      (pre_trivialFibration j hj (D.obj.underlying.enriched.Hom x y))).2

/-- Native mapping precomposition sends every original cofibration to a simplicial fibration. -/
theorem mappingSource_fibration {O : Type u} {A B : FixedStrictDaggerGroupoids O}
    (i : A ⟶ B) [Cofibration i] (D : FixedStrictDaggerGroupoids O) :
    Fibration (eHomWhiskerRight SSet i D) := by
  rw [fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]
  intro K L j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨a⟩⟩ := hj
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1
    (strictRestriction_trivialFibration (SSet.horn (n + 1) a).ι
      (SSet.anodyneExtensions.horn_ι_mem n a) D)
  have : Fibration
      (((strictDaggerCotensorBifunctor O).map (SSet.horn (n + 1) a).ι.op).app D) := hf
  have : WeakEquivalence
      (((strictDaggerCotensorBifunctor O).map (SSet.horn (n + 1) a).ι.op).app D) := hw
  exact mappingSource_lifting (SSet.horn (n + 1) a).ι i D

/-- Maps out of the actual initial strict object form a terminal native simplicial set. -/
def initialMappingIsTerminal {O : Type u} (D : FixedStrictDaggerGroupoids O) :
    IsTerminal ((⊥_ (FixedStrictDaggerGroupoids O)) ⟶[SSet.{u}] D) :=
  IsTerminal.ofUniqueHom
    (fun K ↦ (strictCotensorHomEquiv (⊥_ (FixedStrictDaggerGroupoids O)) D K).symm
      (initial.to (strictDaggerCotensor K D))) (by
        intro K F
        apply (strictCotensorHomEquiv (⊥_ (FixedStrictDaggerGroupoids O)) D K).injective
        rw [Equiv.apply_symm_apply]
        exact initialIsInitial.hom_ext _ _)

/-- The entire native mapping space of every actual cofibrant source is Kan. -/
theorem mapping_kan {O : Type u} (A D : FixedStrictDaggerGroupoids O) [IsCofibrant A] :
    (A ⟶[SSet.{u}] D).KanComplex := by
  have : Cofibration (initial.to A) := (isCofibrant_iff A).1 inferInstance
  have : Fibration (eHomWhiskerRight SSet (initial.to A) D) :=
    mappingSource_fibration (initial.to A) D
  have : IsFibrant (A ⟶[SSet.{u}] D) :=
    (isFibrant_iff_of_isTerminal (eHomWhiskerRight SSet (initial.to A) D)
      (initialMappingIsTerminal D)).2 inferInstance
  infer_instance

end
end DaggerOriginalStrictDaggerMappingCofibrantKan
