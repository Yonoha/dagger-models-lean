import OriginalFixedObjectAmbientDaggerCofreeAdjunction
import OriginalSimplicialTrivialFibrationTensor
import OriginalFixedObjectGroupoidClasses
import OriginalAdjunctionLiftingTransferChallengeProof

/-!
# Ordinary cofibrancy after forgetting the actual ambient dagger

The ordinary fixed-object cofibration class is exactly LLP against all original
Homwise simplicial trivial fibrations, as in DK80's fixed-object model.
The existing full native cofree dagger maps every ordinary Hom to the actual
two-coordinate tensor map. Its trivial-fibration preservation and the native
adjunction prove cofibration preservation. The same adjunction proves the actual
forgotten initial object is initial, giving the object-level cofibrancy result.
No ordinary model-category existence or DK80 localization theorem is assumed.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectAmbientDaggerCofreeAdjunction
open DaggerOriginalFixedObjectAmbientDaggerModel
open DaggerOriginalSimplicialTrivialFibrationTensor
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalAmbientDaggerForgetCofibrancy
noncomputable section

/-- The ordinary trivial fibrations are the exact native class on every original Hom. -/
def ordinaryTrivialFibrations (O : Type u) : MorphismProperty (FixedSimplicialCategory O) :=
  fun _ _ F ↦ ∀ x y : O, trivialFibrations SSet.{u} (F.map x y)

/-- DK80's ordinary fixed-object cofibrations, with precisely the original Homwise tests. -/
def ordinaryCofibrations (O : Type u) : MorphismProperty (FixedSimplicialCategory O) :=
  (ordinaryTrivialFibrations O).llp

/-- Native ordinary cofibration data uses the exact original lifting class. -/
scoped instance ordinaryCofStructure (O : Type u) :
    CategoryWithCofibrations (FixedSimplicialCategory O) := ⟨ordinaryCofibrations O⟩

open scoped DaggerOriginalAmbientDaggerForgetCofibrancy

/-- The ordinary lifting class respects isomorphisms by the native LLP instance. -/
instance ordinaryCofRespectsIso (O : Type u) :
    (ordinaryCofibrations O).RespectsIso := by
  unfold ordinaryCofibrations
  infer_instance

/-- The existing native cofree map is literally the two original coordinate maps. -/
theorem cofreeMap_hom {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D) (x y : O) :
    (ambientCofreeMap F).underlying.map x y = F.map x y ⊗ₘ F.map y x := by
  apply NatTrans.ext
  funext n a
  rfl

/-- The actual original cofree dagger preserves the entire ordinary trivial-fibration class. -/
theorem cofree_trivialFibration {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D)
    (hF : ordinaryTrivialFibrations O F) :
    trivialFibrations (FixedDaggerCategory O) ((ambientCofree O).map F) := by
  have h : ∀ x y : O, trivialFibrations SSet.{u}
      ((ambientCofreeMap F).underlying.map x y) := by
    intro x y
    rw [cofreeMap_hom]
    exact tensorHom_trivialFibration _ _ (hF x y) (hF y x)
  rw [mem_trivialFibrations_iff, fibration_iff_original, weakEquivalence_iff_original]
  exact ⟨fun x y ↦ ((mem_trivialFibrations_iff _).1 (h x y)).1,
    fun x y ↦ ((mem_trivialFibrations_iff _).1 (h x y)).2⟩

/-- The native dagger cofibration has the exact ordinary LLP after forgetting only the dagger. -/
theorem forget_cofibration {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D)
    [Cofibration F] : Cofibration ((ambientForget O).map F) := by
  rw [cofibration_iff]
  have h : (trivialFibrations (FixedDaggerCategory O)).llp F := by
    rw [trivialFibrations_llp]
    exact (cofibration_iff F).1 inferInstance
  exact DaggerOriginalAdjunctionLiftingTransferChallengeProof.challengeProof
    (FixedDaggerCategory O) (FixedSimplicialCategory O) (ambientForget O) (ambientCofree O)
    (ambientForgetCofreeAdjunction O) (ordinaryTrivialFibrations O)
    (trivialFibrations (FixedDaggerCategory O)) (fun p hp ↦ cofree_trivialFibration p hp) F h

/-- The actual underlying object of the native dagger initial object is ordinary initial. -/
def forgottenInitialIsInitial (O : Type u) :
    IsInitial ((ambientForget O).obj (⊥_ (FixedDaggerCategory O))) :=
  IsInitial.ofUniqueHom
    (fun D ↦ (homEquiv (⊥_ (FixedDaggerCategory O)) D).symm
      (initial.to (ambientCofreeObject D))) (by
        intro D F
        apply (homEquiv (⊥_ (FixedDaggerCategory O)) D).injective
        rw [Equiv.apply_symm_apply]
        exact initialIsInitial.hom_ext _ _)

/-- The actual ordinary category has an initial object by the proved full adjunction. -/
instance ordinaryHasInitial (O : Type u) : HasInitial (FixedSimplicialCategory O) :=
  (forgottenInitialIsInitial O).hasInitial

/-- Native cofibrancy of an ambient dagger object implies the exact ordinary fixed-object
cofibrancy required for the localization theorem. -/
theorem forget_isCofibrant {O : Type u} (C : FixedDaggerCategory O) [IsCofibrant C] :
    IsCofibrant ((ambientForget O).obj C) := by
  have : (cofibrations (FixedSimplicialCategory O)).RespectsIso := ordinaryCofRespectsIso O
  have : Cofibration (initial.to C) := (isCofibrant_iff C).1 inferInstance
  have : Cofibration ((ambientForget O).map (initial.to C)) := forget_cofibration (initial.to C)
  exact (isCofibrant_iff_of_isInitial ((ambientForget O).map (initial.to C))
    (forgottenInitialIsInitial O)).2 inferInstance

end
end DaggerOriginalAmbientDaggerForgetCofibrancy
