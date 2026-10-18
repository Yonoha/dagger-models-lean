import OriginalSimplicialPiZeroCategory
import OriginalSimplicialGroupoidCompletionUniversal

/-!
# Actual pi0 categories of all original strict simplicial groupoids

Every original component arrow is represented by an original degree-zero arrow.
Strictness makes that degree-zero arrow invertible. The full native vertex
functor preserves its inverse, so all arrows of the actual component category
are invertible. The native groupoid constructor keeps the entire category.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionUniversal
universe u
namespace DaggerOriginalStrictSimplicialPiZeroGroupoid
noncomputable section

/-- Every actual component arrow in an original strict simplicial groupoid is invertible. -/
theorem componentIsIso_of_strict (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    {x y : componentObjects C} (a : x ⟶ y) : IsIso a := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  let x₀ : degreeObjects C (op ⦋0⦌) := x
  let y₀ : degreeObjects C (op ⦋0⦌) := y
  have := hC (op ⦋0⦌) x₀ y₀ a
  change IsIso ((vertexFunctor C).map (X := x₀) (Y := y₀) a)
  infer_instance

/-- The native groupoid uses exactly the actual component category and its composition. -/
def strictComponentGroupoid (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    Groupoid.{u, u} (componentObjects C) :=
  Groupoid.ofIsIso (fun {_ _} a ↦ componentIsIso_of_strict C hC a)

/-- The entire underlying category is the original transported component category. -/
theorem strictComponentGroupoid_category (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    (strictComponentGroupoid C hC).toCategory = componentCategory C := rfl

/-- Every completed original component category has its actual groupoid structure. -/
def completedComponentGroupoid (C : SimplicialCat.{u, u}) :
    Groupoid.{u, u} (componentObjects (completion C)) :=
  strictComponentGroupoid (completion C) (completion_isStrictGroupoid C)

/-- Completion's component groupoid retains the original completed component composition. -/
theorem completedComponentGroupoid_category (C : SimplicialCat.{u, u}) :
    (completedComponentGroupoid C).toCategory = componentCategory (completion C) := rfl

end
end DaggerOriginalStrictSimplicialPiZeroGroupoid
