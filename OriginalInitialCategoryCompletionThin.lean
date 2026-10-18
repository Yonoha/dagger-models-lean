import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Native groupoid completion of a category with an initial object

Lift the original contraction along Mathlib's native localization. Naturality of
the resulting full isomorphism to a constant functor proves that every completed
Hom is a singleton. No paths, relations or localization are reimplemented.
-/
set_option autoImplicit false
open CategoryTheory Limits
universe u
namespace DaggerOriginalInitialCategoryCompletionThin
noncomputable section
variable {C : Type u} [Category.{u} C]

/-- Initial arrows give an isomorphism from the constant functor to native localization. -/
def originalContraction (c : C) (hc : IsInitial c) :
    (Functor.const C).obj ((FreeGroupoid.of C).obj c) ≅ FreeGroupoid.of C := by
  refine NatIso.ofComponents (fun x ↦ asIso ((FreeGroupoid.of C).map (hc.to x))) ?_
  intro x y f
  change 𝟙 _ ≫ (FreeGroupoid.of C).map (hc.to y) =
    (FreeGroupoid.of C).map (hc.to x) ≫ (FreeGroupoid.of C).map f
  rw [Category.id_comp, ← Functor.map_comp]
  exact congrArg (FreeGroupoid.of C).map (hc.hom_ext _ _)

/-- The native localization universal property lifts the entire contraction isomorphism. -/
def completedContraction (c : C) (hc : IsInitial c) :
    (Functor.const (FreeGroupoid C)).obj ((FreeGroupoid.of C).obj c) ≅
      𝟭 (FreeGroupoid C) :=
  FreeGroupoid.liftNatIso _ _ (originalContraction c hc)

/-- All original completed Hom arrows are equal, by full lifted naturality. -/
def completionIsThin (c : C) (hc : IsInitial c) : Quiver.IsThin (FreeGroupoid C) := by
  intro x y
  constructor
  intro f g
  apply (cancel_epi ((completedContraction c hc).hom.app x)).1
  exact ((completedContraction c hc).hom.naturality f).symm.trans
    ((completedContraction c hc).hom.naturality g)

/-- The same full contraction supplies a morphism between every pair of completed objects. -/
theorem completionHomNonempty (c : C) (hc : IsInitial c) (x y : FreeGroupoid C) :
    Nonempty (x ⟶ y) :=
  ⟨(completedContraction c hc).inv.app x ≫ (completedContraction c hc).hom.app y⟩

end
end DaggerOriginalInitialCategoryCompletionThin
