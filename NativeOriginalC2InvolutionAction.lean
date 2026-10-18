import OriginalCompletedDaggerMappingAction

/-! A generic native action from an involution, using the UNCHANGED original C2 laws. -/
set_option autoImplicit false
open CategoryTheory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
universe u v w
namespace DaggerNativeOriginalC2InvolutionAction
noncomputable section
variable {C : Type u} [Category.{v} C]

def representation {X : C} (s : End X) (hs : s * s = 1) : C2.{w} →* End X where
  toFun g := if g = 1 then 1 else s
  map_one' := by simp
  map_mul' g h := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    rcases originalC2_cases h with rfl | rfl
    · simp
    simp [originalGenerator_mul_self, originalGenerator_ne_one, hs]

theorem representation_generator {X : C} (s : End X) (hs : s * s = 1) :
    representation s hs generator.{w} = s := by
  simp [representation, originalGenerator_ne_one]

def action {X : C} (s : End X) (hs : s * s = 1) : Action C C2.{w} :=
  ⟨X, representation s hs⟩

theorem action_generator {X : C} (s : End X) (hs : s * s = 1) :
    (action s hs).ρ generator.{w} = s := representation_generator s hs

def map {X Y : C} (s : End X) (hs : s * s = 1) (t : End Y) (ht : t * t = 1)
    (f : X ⟶ Y) (hf : s ≫ f = f ≫ t) : action.{u, v, w} s hs ⟶ action t ht where
  hom := f
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · simp [action, representation]
    · simpa only [action_generator] using hf

end
end DaggerNativeOriginalC2InvolutionAction
