import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.Core

/-!
# A candidate for the ordinary maximal Kan core

This is the literal preimage of the nerve of the ordinary categorical core
along the unit from a simplicial set to the nerve of its homotopy category.
No Kan or maximality property is asserted here.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalOrdinaryKanCoreSubcomplex

noncomputable section

/-- The actual unit of the retained homotopy-category/nerve adjunction. -/
def homotopyCategoryUnit (X : SSet.{u}) :
    X ⟶ CategoryTheory.nerve (SSet.hoFunctor.obj X) :=
  (CategoryTheory.nerveAdjunction).unit.app X

/-- The nerve of the ordinary categorical core enters the nerve of the
actual homotopy category of `X`. -/
def nerveCoreInclusion (X : SSet.{u}) :
    CategoryTheory.nerve (CategoryTheory.Core (SSet.hoFunctor.obj X)) ⟶
      CategoryTheory.nerve (SSet.hoFunctor.obj X) :=
  CategoryTheory.nerveMap
    (CategoryTheory.Core.inclusion (SSet.hoFunctor.obj X))

/-- The degreewise range of the nerve of the ordinary categorical core. -/
def nerveCoreRange (X : SSet.{u}) :
    (CategoryTheory.nerve (SSet.hoFunctor.obj X)).Subcomplex :=
  SSet.Subcomplex.range (nerveCoreInclusion X)

/-- The preimage candidate for the ordinary quasi-categorical core.
Its Kan and maximality properties remain to be proved. -/
def ordinaryCoreCandidate (X : SSet.{u}) : X.Subcomplex :=
  (nerveCoreRange X).preimage (homotopyCategoryUnit X)

/-- The candidate has precisely the simplices whose image under the actual
homotopy-category unit lies in the nerve of the ordinary core. -/
theorem mem_ordinaryCoreCandidate_iff (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (s : X.obj n) :
    s ∈ (ordinaryCoreCandidate X).obj n ↔
      ∃ t : (CategoryTheory.nerve
          (CategoryTheory.Core (SSet.hoFunctor.obj X))).obj n,
        (nerveCoreInclusion X).app n t = (homotopyCategoryUnit X).app n s := by
  rfl

/-- The comparison morphism into the actual nerve-core range. -/
def candidateToNerveCore (X : SSet.{u}) :
    (ordinaryCoreCandidate X : SSet.{u}) ⟶
      (nerveCoreRange X : SSet.{u}) :=
  (nerveCoreRange X).fromPreimage (homotopyCategoryUnit X)

@[reassoc]
theorem candidateToNerveCore_comp (X : SSet.{u}) :
    candidateToNerveCore X ≫ (nerveCoreRange X).ι =
      (ordinaryCoreCandidate X).ι ≫ homotopyCategoryUnit X :=
  SSet.Subcomplex.fromPreimage_ι (nerveCoreRange X) (homotopyCategoryUnit X)

/-- The candidate contains every vertex of `X`, since the ordinary
categorical core has all objects of the homotopy category. -/
theorem vertex_mem_ordinaryCoreCandidate (X : SSet.{u})
    (x : X.obj (op ⦋0⦌)) :
    x ∈ (ordinaryCoreCandidate X).obj (op ⦋0⦌) := by
  let y := (homotopyCategoryUnit X).app (op ⦋0⦌) x
  let t : (CategoryTheory.nerve
      (CategoryTheory.Core (SSet.hoFunctor.obj X))).obj (op ⦋0⦌) :=
    CategoryTheory.ComposableArrows.mk₀
      (CategoryTheory.Core.mk (CategoryTheory.nerveEquiv y))
  apply (mem_ordinaryCoreCandidate_iff X (op ⦋0⦌) x).2
  refine ⟨t, ?_⟩
  apply CategoryTheory.nerveEquiv.injective
  rfl

end

end DaggerOriginalOrdinaryKanCoreSubcomplex
