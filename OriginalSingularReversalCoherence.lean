import OriginalSingularSetReversal

/-!
# Double reversal for the actual singular simplicial set

The comparison is with Mathlib's actual double-op natural isomorphism.
The parameter reversal calculation is independent of any realization
or dagger action on a topological space.
-/

set_option autoImplicit false

open CategoryTheory Opposite

universe u

namespace DaggerOriginalSingularReversalCoherence

open DaggerOriginalTopologicalSimplexReversal
open DaggerOriginalSingularSetReversal

noncomputable section

/-- Inverse and forward topological parameter reversal are the same map. -/
theorem reversalIso_inv_eq_hom (n : SimplexCategory) :
    reversalIso.{u}.inv.app n = reversalIso.{u}.hom.app n := by
  have hs := reversalIso_hom_sq.{u} n
  have hi := reversalIso.{u}.hom_inv_id_app n
  calc
    reversalIso.{u}.inv.app n =
        𝟙 _ ≫ reversalIso.{u}.inv.app n := (Category.id_comp _).symm
    _ = (reversalIso.{u}.hom.app n ≫ reversalIso.{u}.hom.app n) ≫
        reversalIso.{u}.inv.app n := by rw [hs]
    _ = reversalIso.{u}.hom.app n ≫
        (reversalIso.{u}.hom.app n ≫ reversalIso.{u}.inv.app n) :=
      Category.assoc _ _ _
    _ = reversalIso.{u}.hom.app n ≫ 𝟙 _ := by
      rw [hi]
      rfl
    _ = reversalIso.{u}.hom.app n := Category.comp_id _

/-- Twice reversing an actual singular simplex is Mathlib's double-op map. -/
theorem singularReversal_square (X : TopCat.{u}) :
    SSet.opFunctor.map (singularReversal.hom.app X) ≫
      singularReversal.hom.app X =
        SSet.opFunctorCompOpFunctorIso.hom.app (TopCat.toSSet.obj X) := by
  ext n α
  apply ULift.ext
  change reversalIso.{u}.inv.app n.unop ≫
    (reversalIso.{u}.inv.app n.unop ≫ α.down) = α.down
  rw [← Category.assoc]
  simp only [reversalIso_inv_eq_hom, reversalIso_hom_sq, Category.id_comp]

end

end DaggerOriginalSingularReversalCoherence
