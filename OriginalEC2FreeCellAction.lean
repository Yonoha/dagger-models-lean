import OriginalEC2SkeletonAction
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The regular action on the actual constant cell coproducts

Left multiplication permutes the C2 indices while acting identically on each
simplex or boundary. This supplies the action on the already checked attaching
square's two left objects, without asserting a model cofibration.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action

universe u

namespace DaggerOriginalEC2FreeCellAction

noncomputable section

private def cellPermutation (A : SSet.{u}) (h : C2.{u}) :
    (∐ (fun (_ : C2.{u}) ↦ A)) ⟶ (∐ (fun (_ : C2.{u}) ↦ A)) :=
  Limits.Sigma.desc (fun g ↦ Limits.Sigma.ι (fun (_ : C2.{u}) ↦ A) (h * g))

private theorem ι_cellPermutation (A : SSet.{u}) (h g : C2.{u}) :
    Limits.Sigma.ι (fun (_ : C2.{u}) ↦ A) g ≫ cellPermutation A h =
      Limits.Sigma.ι (fun (_ : C2.{u}) ↦ A) (h * g) :=
  Limits.Sigma.ι_desc _ g

/-- The literal left regular permutation action on a C2-indexed cell coproduct. -/
def freeCellAction (A : SSet.{u}) : Action SSet.{u} C2.{u} where
  V := ∐ (fun (_ : C2.{u}) ↦ A)
  ρ :=
    { toFun := fun h ↦ End.of (cellPermutation A h)
      map_one' := by
        apply End.ext
        apply Limits.Sigma.hom_ext
        intro g
        simp only [ι_cellPermutation, one_mul, Category.comp_id, End.one_def]
      map_mul' := by
        intro h k
        apply End.ext
        change cellPermutation A (h * k) = cellPermutation A k ≫ cellPermutation A h
        apply Limits.Sigma.hom_ext
        intro g
        simp only [ι_cellPermutation, ← Category.assoc, mul_assoc] }

/-- Acting on the g component gives exactly the h*g component with no cell map. -/
theorem freeCellAction_ι (A : SSet.{u}) (h g : C2.{u}) :
    Limits.Sigma.ι (fun (_ : C2.{u}) ↦ A) g ≫ (freeCellAction A).ρ h =
      Limits.Sigma.ι (fun (_ : C2.{u}) ↦ A) (h * g) :=
  ι_cellPermutation A h g

/-- A literal cell map applied on all components is equivariant. -/
def freeCellMap {A B : SSet.{u}} (f : A ⟶ B) :
    freeCellAction A ⟶ freeCellAction B where
  hom := Limits.Sigma.map (fun (_ : C2.{u}) ↦ f)
  comm h := by
    apply Limits.Sigma.hom_ext
    intro g
    rw [← Category.assoc, freeCellAction_ι]
    rw [Limits.Sigma.ι_map]
    rw [Limits.Sigma.ι_map_assoc]
    rw [freeCellAction_ι]

/-- The equivariant cell map has exactly the componentwise coproduct map. -/
theorem freeCellMap_hom {A B : SSet.{u}} (f : A ⟶ B) :
    (freeCellMap f).hom = Limits.Sigma.map (fun (_ : C2.{u}) ↦ f) := rfl

end

end DaggerOriginalEC2FreeCellAction
