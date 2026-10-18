import NativeAmbientDaggerRelativeCotensor
import OriginalFixedObjectCotensorTargetNaturality

/-! Lift ENTIRE original target mapping squares through the actual relative cotensor.
No derived mapping recognition or simplicial-model axiom is assumed.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectDaggerCotensorRepresentation
open DaggerOriginalFixedObjectCotensorTargetNaturality
open DaggerNativeAmbientDaggerRelativeCotensor
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeAmbientDaggerMappingTargetLifting
noncomputable section

theorem mappingTarget_lifting {O : Type u} {K L : SSet.{u}} (j : K ⟶ L)
    (A : FixedDaggerCategory O) {C D : FixedDaggerCategory O} (p : C ⟶ D)
    [HasLiftingProperty (initial.to A) (relativeMap j p)] :
    HasLiftingProperty j (eHomWhiskerLeft SSet A p) := by
  constructor
  intro f g sq
  have h : cotensorHomEquiv A C K f ≫ daggerCotensorMap K p =
      cotensorHomEquiv A D L g ≫ daggerCotensorPre j D := by
    rw [← daggerCotensorHomEquiv_target, ← cotensorHomEquiv_parameter]
    exact congrArg (cotensorHomEquiv A D K) sq.w
  let b : A ⟶ target j p :=
    pullback.lift (cotensorHomEquiv A C K f) (cotensorHomEquiv A D L g) h
  let sq' : CommSq (initial.to (daggerCotensor L C)) (initial.to A) (relativeMap j p) b :=
    ⟨initialIsInitial.hom_ext _ _⟩
  let l := (cotensorHomEquiv A C L).symm sq'.lift
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (cotensorHomEquiv A C K).injective
    rw [cotensorHomEquiv_parameter]
    change (cotensorHomEquiv A C L) ((cotensorHomEquiv A C L).symm sq'.lift) ≫ _ = _
    rw [Equiv.apply_symm_apply, ← relativeMap_fst j p, ← Category.assoc, sq'.fac_right]
    exact pullback.lift_fst _ _ _
  · apply (cotensorHomEquiv A D L).injective
    rw [daggerCotensorHomEquiv_target]
    change (cotensorHomEquiv A C L) ((cotensorHomEquiv A C L).symm sq'.lift) ≫ _ = _
    rw [Equiv.apply_symm_apply, ← relativeMap_snd j p, ← Category.assoc, sq'.fac_right]
    exact pullback.lift_snd _ _ _

theorem mappingTarget_trivialFibration {O : Type u} (A : FixedDaggerCategory O)
    [IsCofibrant A] {C D : FixedDaggerCategory O} (p : C ⟶ D)
    [Fibration p] [WeakEquivalence p] :
    trivialFibrations SSet.{u} (eHomWhiskerLeft SSet A p) := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  rintro _ _ _ ⟨n⟩
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp
    (relativeMap_trivialFibration (SSet.boundary n).ι p)
  have : Fibration (relativeMap (SSet.boundary n).ι p) := hf
  have : WeakEquivalence (relativeMap (SSet.boundary n).ι p) := hw
  have : Cofibration (initial.to A) := (isCofibrant_iff A).mp inferInstance
  exact mappingTarget_lifting (SSet.boundary n).ι A p

theorem mappingTarget_fibration {O : Type u} (A : FixedDaggerCategory O)
    [IsCofibrant A] {C D : FixedDaggerCategory O} (p : C ⟶ D) [Fibration p] :
    Fibration (eHomWhiskerLeft SSet A p) := by
  rw [fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]
  intro K L j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨a⟩⟩ := hj
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).mp
    (relativeMap_anodyne_trivialFibration (SSet.horn (n + 1) a).ι p
      (SSet.anodyneExtensions.horn_ι_mem n a))
  have : Fibration (relativeMap (SSet.horn (n + 1) a).ι p) := hf
  have : WeakEquivalence (relativeMap (SSet.horn (n + 1) a).ι p) := hw
  have : Cofibration (initial.to A) := (isCofibrant_iff A).mp inferInstance
  exact mappingTarget_lifting (SSet.horn (n + 1) a).ι A p

end
end DaggerNativeAmbientDaggerMappingTargetLifting
