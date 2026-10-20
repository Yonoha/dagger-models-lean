import OriginalTaggedReverseAntiPresheaf
import OriginalTaggedReversePrecomposition
import DaggerModels.Presheaf

/-!
# The actual tagged quotient realizes the original dagger inclusion

The comparison is a natural isomorphism of functors on existing categories.
Every component is the identity on the underlying simplices.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.OriginalTaggedReversePresheafInclusion

open DaggerModels.OriginalTaggedReverseSimplex
open TaggedReverseSimplex
open DaggerModels.OriginalTaggedReversePrecomposition

/-- The route through the original reversal and tagged presheaves. -/
noncomputable def presheafRoute :
    DaggerSSet.{u} ⥤ AntiInvolutiveSSet.{u} :=
  DaggerSSet.toPresheaf ⋙ precomposition (Type u) ⋙
    TaggedPresheaf.toAntiInvolutive

theorem restrictedMap (X : DaggerSSet.{u}) {m n : SimplexCategory}
    (f : m ⟶ n) (x : X.toSSet.obj (op n)) :
    ((presheafRoute.obj X).toSSet.map f.op) x = X.toSSet.map f.op x := by
  have hmap : qTag.map (simplexInclusion.map f) =
      ReverseSimplex.inclusion.map f := by
    exact eq_of_heq (Functor.hcongr_hom qTag_inclusion f)
  change X.extension.map (qTag.map (simplexInclusion.map f)).op x = _
  rw [hmap]
  exact X.extension_inclusion f x

theorem restrictedDagger (X : DaggerSSet.{u}) (n : ℕ)
    (x : X.toSSet _⦋n⦌) :
    (presheafRoute.obj X).daggerSimplex x = X.daggerSimplex x := by
  change X.extension.map (qTag.map (taggedReversal ⟨n⟩)).op x = _
  rw [qTag_taggedReversal]
  exact X.extension_reversal ⟨n⟩ x

/-- Identity simplex maps compare both original anti-involutive structures. -/
noncomputable def comparisonComponent (X : DaggerSSet.{u}) :
    presheafRoute.obj X ≅ DaggerSSet.toAntiInvolutive.obj X where
  hom :=
    { hom :=
        { app := fun _ ↦ id
          naturality := fun {n m} f ↦ by
            funext x
            exact restrictedMap X f.unop x }
      comm := by
        ext n x
        exact (restrictedDagger X n.unop.len x).symm }
  inv :=
    { hom :=
        { app := fun _ ↦ id
          naturality := fun {n m} f ↦ by
            funext x
            exact (restrictedMap X f.unop x).symm }
      comm := by
        ext n x
        exact restrictedDagger X n.unop.len x }
  hom_inv_id := by apply AntiInvolutiveSSet.Hom.ext; ext n x; rfl
  inv_hom_id := by apply AntiInvolutiveSSet.Hom.ext; ext n x; rfl

/-- Precomposition by the actual `qTag.op` commutes with the original inclusion. -/
noncomputable def comparisonIso :
    presheafRoute ≅ DaggerSSet.toAntiInvolutive :=
  NatIso.ofComponents comparisonComponent (by
    intro X Y f
    apply AntiInvolutiveSSet.Hom.ext
    ext n x
    rfl)

theorem comparisonComponent_hom_app (X : DaggerSSet.{u})
    (n : SimplexCategoryᵒᵖ) (x : X.toSSet.obj n) :
    (comparisonComponent X).hom.hom.app n x = x := rfl

theorem comparisonComponent_inv_app (X : DaggerSSet.{u})
    (n : SimplexCategoryᵒᵖ) (x : X.toSSet.obj n) :
    (comparisonComponent X).inv.hom.app n x = x := rfl

end DaggerModels.OriginalTaggedReversePresheafInclusion
