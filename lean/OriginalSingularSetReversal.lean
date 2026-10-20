import OriginalTopologicalSimplexReversal
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
# Reversal of the actual singular simplicial set

The component acts on a singular simplex by precomposition with reversal
of its topological standard-simplex parameter. The comparison is natural
both in the simplex degree and in the topological space.
-/

set_option autoImplicit false

open CategoryTheory Opposite

universe u

namespace DaggerOriginalSingularSetReversal

open DaggerOriginalTopologicalSimplexReversal

noncomputable section

/-- Reverse the parameter of an actual singular simplex. -/
def componentHom (X : TopCat.{u}) :
    (TopCat.toSSet.obj X).op ⟶ TopCat.toSSet.obj X where
  app n α := ULift.up (reversalIso.{u}.inv.app n.unop ≫ α.down)
  naturality {n m} f := by
    funext α
    apply ULift.ext
    change (reversalIso.{u}.inv.app m.unop ≫
      SimplexCategory.toTop.{u}.map (SimplexCategory.rev.map f.unop)) ≫ α.down =
        (SimplexCategory.toTop.{u}.map f.unop ≫
          reversalIso.{u}.inv.app n.unop) ≫ α.down
    apply congrArg (fun k ↦ k ≫ α.down)
    simpa only [CategoryTheory.Functor.comp_map] using
      (reversalIso.{u}.inv.naturality f.unop).symm

/-- The inverse parameter change uses the other side of the simplex iso. -/
def componentInv (X : TopCat.{u}) :
    TopCat.toSSet.obj X ⟶ (TopCat.toSSet.obj X).op where
  app n α := ULift.up (reversalIso.{u}.hom.app n.unop ≫ α.down)
  naturality {n m} f := by
    funext α
    apply ULift.ext
    change (reversalIso.{u}.hom.app m.unop ≫
      SimplexCategory.toTop.{u}.map f.unop) ≫ α.down =
        (SimplexCategory.toTop.{u}.map (SimplexCategory.rev.map f.unop) ≫
          reversalIso.{u}.hom.app n.unop) ≫ α.down
    apply congrArg (fun k ↦ k ≫ α.down)
    simpa only [CategoryTheory.Functor.comp_map] using
      (reversalIso.{u}.hom.naturality f.unop).symm

/-- The singular-set parameter reversal is an isomorphism at every space. -/
def componentIso (X : TopCat.{u}) :
    (TopCat.toSSet.obj X).op ≅ TopCat.toSSet.obj X where
  hom := componentHom X
  inv := componentInv X
  hom_inv_id := by
    ext n α
    apply ULift.ext
    change (reversalIso.{u}.hom.app n.unop ≫
      reversalIso.{u}.inv.app n.unop) ≫ α.down = α.down
    rw [reversalIso.{u}.hom_inv_id_app, Category.id_comp]
  inv_hom_id := by
    ext n α
    apply ULift.ext
    change (reversalIso.{u}.inv.app n.unop ≫
      reversalIso.{u}.hom.app n.unop) ≫ α.down = α.down
    rw [reversalIso.{u}.inv_hom_id_app, Category.id_comp]

/-- Natural reversal of the existing singular simplicial-set functor. -/
def singularReversal :
    TopCat.toSSet.{u} ⋙ SSet.opFunctor.{u} ≅ TopCat.toSSet.{u} :=
  NatIso.ofComponents componentIso (by
    intro X Y g
    ext n α
    apply ULift.ext
    change (reversalIso.{u}.inv.app n.unop ≫ α.down) ≫ g =
      reversalIso.{u}.inv.app n.unop ≫ (α.down ≫ g)
    exact Category.assoc _ _ _)

/-- Forward component on a literal `ULift` singular simplex. -/
theorem singularReversal_hom_app (X : TopCat.{u})
    (n : SimplexCategoryᵒᵖ)
    (α : (TopCat.toSSet.obj X).op.obj n) :
    (singularReversal.{u}.hom.app X).app n α =
      ULift.up (reversalIso.{u}.inv.app n.unop ≫ α.down) := rfl

/-- Inverse component on a literal `ULift` singular simplex. -/
theorem singularReversal_inv_app (X : TopCat.{u})
    (n : SimplexCategoryᵒᵖ)
    (α : (TopCat.toSSet.obj X).obj n) :
    (singularReversal.{u}.inv.app X).app n α =
      ULift.up (reversalIso.{u}.hom.app n.unop ≫ α.down) := rfl

end

end DaggerOriginalSingularSetReversal
