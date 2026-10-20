import OriginalActionFreeForgetAdjunction
import OriginalActionForgetCofreeAdjunction
import OriginalDaggerRealizationC2Action
import TopCatModelCategory.ModelCategorySSet

/-!
# Original free boundaries and horns for projective C₂-simplicial actions

The generators are free actions on the literal original simplicial boundaries and horns.
The native free/forgetful adjunction identifies their right lifting classes with fibrations
and trivial fibrations of the unchanged underlying simplicial maps. Cofree product lifting
proves underlying acyclicity of the complete free-horn left class without assuming the
projective action model structure.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalActionFreeForgetAdjunction
open DaggerOriginalActionForgetCofreeAdjunction
open scoped SSet.modelCategoryQuillen

universe u v

namespace DaggerOriginalSimplicialActionFreeGenerators

noncomputable section

/-- The native regular free simplicial C₂-action functor. -/
abbrev free : SSet.{u} ⥤ Action SSet.{u} C2.{u} := freeActionFunctor SSet.{u} C2.{u}

/-- Free actions on the original simplicial boundary inclusions. -/
def I : MorphismProperty (Action SSet.{u} C2.{u}) :=
  ofHoms (fun n ↦ free.map (SSet.boundary.{u} n).ι)

/-- Free actions on the original positive-dimensional simplicial horn inclusions. -/
def J : MorphismProperty (Action SSet.{u} C2.{u}) :=
  ⨆ n, ofHoms (fun i ↦ free.map (SSet.horn.{u} (n + 1) i).ι)

instance I_isSmall : IsSmall.{v} I.{u} := by dsimp [I]; infer_instance
instance J_isSmall : IsSmall.{v} J.{u} := by dsimp [J]; infer_instance

/-- Free boundary lifting is literal boundary lifting of the same underlying simplicial map. -/
theorem I_rlp_iff {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) :
    I.rlp p ↔ SSet.modelCategoryQuillen.I.rlp p.hom := by
  constructor
  · rintro hp _ _ _ ⟨n⟩
    rw [← freeAction_lifting_iff SSet.{u} C2.{u}]
    exact hp _ ⟨n⟩
  · rintro hp _ _ _ ⟨n⟩
    rw [freeAction_lifting_iff SSet.{u} C2.{u}]
    exact hp _ ⟨n⟩

/-- Free horn lifting is literal horn lifting of the same underlying simplicial map. -/
theorem J_rlp_iff {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) :
    J.rlp p ↔ SSet.modelCategoryQuillen.J.rlp p.hom := by
  constructor
  · intro hp _ _ _ h
    simp only [SSet.modelCategoryQuillen.J, iSup_iff] at h
    obtain ⟨n, ⟨i⟩⟩ := h
    rw [← freeAction_lifting_iff SSet.{u} C2.{u}]
    apply hp
    simp only [J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩
  · intro hp _ _ _ h
    simp only [J, iSup_iff] at h
    obtain ⟨n, ⟨i⟩⟩ := h
    rw [freeAction_lifting_iff SSet.{u} C2.{u}]
    apply hp
    simp only [SSet.modelCategoryQuillen.J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩

/-- Free boundary right lifting is exactly underlying native trivial fibration. -/
theorem I_rlp_iff_trivialFibration {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) :
    I.rlp p ↔ Fibration p.hom ∧ WeakEquivalence p.hom := by
  rw [I_rlp_iff, SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations,
    mem_trivialFibrations_iff]

/-- Free horn right lifting is exactly underlying native fibration. -/
theorem J_rlp_iff_fibration {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) :
    J.rlp p ↔ Fibration p.hom := by
  rw [J_rlp_iff, fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]

/-- Free boundary right lifting implies free horn right lifting on the same action arrow. -/
theorem I_rlp_le_J_rlp : I.{u}.rlp ≤ J.{u}.rlp := by
  intro X Y p hp
  exact (J_rlp_iff_fibration p).2 ((I_rlp_iff_trivialFibration p).1 hp).1

/-- Native product lifting gives free-horn lifting for the cofree image of a fibration. -/
theorem cofree_map_J_rlp {A B : SSet.{u}} (p : A ⟶ B) (hp : Fibration p) :
    J.rlp ((cofreeActionFunctor SSet.{u} C2.{u}).map p) := by
  rw [J_rlp_iff, cofreeAction_map_hom]
  intro X Y i hi
  have h : SSet.modelCategoryQuillen.J.rlp p := by
    rwa [← SSet.modelCategoryQuillen.fibrations_eq, ← fibration_iff]
  have : HasLiftingProperty i p := h i hi
  exact inferInstance

/-- The complete free-horn left class is a trivial cofibration on the original underlying map.
-/
theorem J_rlp_llp_underlying_trivialCofibration {X Y : Action SSet.{u} C2.{u}}
    (i : X ⟶ Y) (hi : J.rlp.llp i) : trivialCofibrations SSet.{u} i.hom := by
  rw [← fibrations_llp SSet.{u}]
  intro A B p hp
  rw [forget_lifting_iff SSet.{u} C2.{u} i p]
  exact hi _ (cofree_map_J_rlp p ((fibration_iff p).2 hp))

/-- The complete free-horn left class is weakly equivalent on the same underlying map. -/
theorem J_rlp_llp_underlying_weakEquivalence {X Y : Action SSet.{u} C2.{u}}
    (i : X ⟶ Y) (hi : J.rlp.llp i) : WeakEquivalence i.hom :=
  (mem_trivialCofibrations_iff i.hom).1 (J_rlp_llp_underlying_trivialCofibration i hi) |>.2

end

end DaggerOriginalSimplicialActionFreeGenerators
