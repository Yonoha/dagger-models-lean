import OriginalSimplicialGroupoidCompletionDaggerFunctor
import OriginalDaggerRealizationC2Action

/-!
# The actual completed dagger mapping object with the original C₂-action

Use the project's unchanged acting group and the full completed covariant involution.
The action generator is precisely inverse completed dagger. Every original dagger
functor induces an equivariant map with the original completed simplicial Hom map.
This construction does not assume or assert mapping-space fibrancy.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionFunctor
open DaggerOriginalSimplicialGroupoidCompletionSigma
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor

universe u

namespace DaggerOriginalCompletedDaggerMappingAction

noncomputable section

/-- The unchanged project group has exactly the original identity and generator. -/
theorem originalC2_cases (g : C2.{u}) : g = 1 ∨ g = generator := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz (Multiplicative.toAdd g.down) with h | h
  · left
    exact ULift.down_injective h
  · right
    exact ULift.down_injective h

/-- The unchanged original generator is nontrivial. -/
theorem originalGenerator_ne_one : generator.{u} ≠ 1 := by decide

/-- The unchanged original generator squares to the identity. -/
theorem originalGenerator_mul_self : generator.{u} * generator = 1 := by decide

/-- The original acting group acts by the full completed covariant involution. -/
def completedMappingAction (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    Action SSet.{u} C2.{u} where
  V := completedHom C.toSimplicialCat x y
  ρ :=
    { toFun := fun g ↦ if g = 1 then 1 else End.of (completedSigmaHom C x y)
      map_one' := by simp
      map_mul' := fun g h ↦ by
        rcases originalC2_cases g with rfl | rfl
        · simp
        rcases originalC2_cases h with rfl | rfl
        · simp
        simp [originalGenerator_mul_self, originalGenerator_ne_one, End.mul_def,
          completedSigmaHom_involutive] }

/-- The actual action generator is exactly the full completed covariant involution. -/
theorem completedMappingAction_generator (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    ((completedMappingAction C x y).ρ generator).asHom = completedSigmaHom C x y := by
  simp [completedMappingAction, originalGenerator_ne_one]

/-- On every degree the actual action is inverse of the actual extended dagger. -/
theorem completedMappingAction_generator_degree (C : DaggerSimplicialCat.{u, u})
    (x y : C.Obj) (n : SimplexCategoryᵒᵖ)
    (f : (completedHom C.toSimplicialCat x y).obj n) :
    (((completedMappingAction C x y).ρ generator).asHom).app n f =
      inv ((completedDaggerHom C x y).app n f) := by
  rw [completedMappingAction_generator]
  change (completedSigmaDegree C n).map f = inv (inv ((completedSigmaDegree C n).map f))
  exact IsIso.inv_inv.symm

/-- Every original completion Hom map intertwines the full completed involutions. -/
theorem completionHomMap_sigma {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (x y : C.Obj) :
    completedSigmaHom C x y ≫ completionHomMap F.toEnrichedFunctor x y =
      completionHomMap F.toEnrichedFunctor x y ≫ completedSigmaHom D (F.obj x) (F.obj y) := by
  ext n f
  have h := CategoryTheory.Functor.congr_hom (completedSigmaDegree_functor F n) f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.comp_map] using h.symm

/-- The original completed Hom map of a dagger functor is an actual C₂-equivariant map. -/
def completedMappingActionMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (x y : C.Obj) : completedMappingAction C x y ⟶ completedMappingAction D (F.obj x) (F.obj y)
    where
  hom := completionHomMap F.toEnrichedFunctor x y
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    · simpa only [completedMappingAction_generator] using completionHomMap_sigma F x y

end

end DaggerOriginalCompletedDaggerMappingAction
