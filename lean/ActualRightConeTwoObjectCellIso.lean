import ActualRightConeDiagonalHoms
import ActualRightConeReverseHom
import DaggerModels.OrdinaryTwoObjectCell
import ChosenEnrichedSpecifiedIso

/-! The actual rigidified right cone is the original ordinary two-object cell on its Q Hom. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory MonoidalCategory
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightCone
open DaggerActualRightConeObjectClassification DaggerActualRightConeDiagonalHoms
open DaggerChosenRigidificationNecklace hiding C RV
universe u

namespace DaggerActualRightConeTwoObjectCellIso
noncomputable section

/-- Use the existing one-edge universal property, keeping the literal original Q Hom. -/
def cellToCone (n : ℕ) : OrdinaryTwoObjectCell.cell (Q.{u} n) ⟶
    rigidification.{u}.obj (cone.{u} n) :=
  OrdinaryTwoObjectCell.fromData (Q n) _ (alphaObj n) (omegaObj n) (𝟙 (Q n))

theorem cellToCone_obj (n : ℕ) (x : TwoObjectDaggerGraph.Vertex.{u}) :
    (cellToCone.{u} n).obj x = objectEquiv n x.down := by
  rcases x with ⟨b⟩
  cases b <;> rfl

theorem cellToCone_object_bijective (n : ℕ) :
    Function.Bijective (cellToCone.{u} n).obj := by
  have h : (cellToCone.{u} n).obj =
      (Equiv.ulift.trans (objectEquiv.{u} n)) := funext (cellToCone_obj n)
  rw [h]
  exact (Equiv.ulift.trans (objectEquiv.{u} n)).bijective

theorem cellToCone_forward_Hom (n : ℕ) :
    (cellToCone.{u} n).map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right =
      𝟙 (Q.{u} n) := rfl

theorem cellToCone_Hom_isIso (n : ℕ) (x y : TwoObjectDaggerGraph.Vertex.{u}) :
    IsIso ((cellToCone.{u} n).map x y) := by
  rcases x with ⟨b⟩
  rcases y with ⟨c⟩
  cases b <;> cases c
  · change IsIso ((cellToCone n).map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.left)
    let e := (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).uniqueUpToIso
      (alpha_isTerminal n)
    have h : (cellToCone n).map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.left =
        e.hom := (alpha_isTerminal n).hom_ext _ _
    rw [h]
    infer_instance
  · change IsIso (𝟙 (Q.{u} n))
    infer_instance
  · change IsIso ((cellToCone n).map TwoObjectDaggerGraph.right TwoObjectDaggerGraph.left)
    have ht : IsInitial TwoObjectDaggerGraph.empty.{u} := by
      refine IsInitial.ofUniqueHom TwoObjectDaggerGraph.emptyMap ?_
      intro X f
      ext q x
      exact PEmpty.elim x
    let e := ht.uniqueUpToIso (DaggerActualRightConeReverseHom.isInitial n)
    have h : (cellToCone n).map TwoObjectDaggerGraph.right TwoObjectDaggerGraph.left =
        e.hom := ht.hom_ext _ _
    rw [h]
    infer_instance
  · change IsIso ((cellToCone n).map TwoObjectDaggerGraph.right TwoObjectDaggerGraph.right)
    let e := (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).uniqueUpToIso
      (omega_isTerminal n)
    have h : (cellToCone n).map TwoObjectDaggerGraph.right TwoObjectDaggerGraph.right =
        e.hom := (omega_isTerminal n).hom_ext _ _
    rw [h]
    infer_instance

/-- All object and Hom data are the ones of the original fromData functor. -/
def cellIsoData (n : ℕ) : SpecifiedEnrichedIsoData
    (OrdinaryTwoObjectCell.cell (Q.{u} n)) (rigidification.{u}.obj (cone.{u} n)) where
  objects := Equiv.ofBijective (cellToCone n).obj (cellToCone_object_bijective n)
  homs x y := by
    have : IsIso ((cellToCone n).map x y) := cellToCone_Hom_isIso n x y
    exact asIso ((cellToCone n).map x y)
  hom_id := (cellToCone n).map_id
  hom_comp := (cellToCone n).map_comp

def cellIso (n : ℕ) : OrdinaryTwoObjectCell.cell (Q.{u} n) ≅
    rigidification.{u}.obj (cone.{u} n) := (cellIsoData n).iso

theorem cellIso_hom (n : ℕ) : (cellIso.{u} n).hom = cellToCone.{u} n := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro x y
  rfl

end
end DaggerActualRightConeTwoObjectCellIso
