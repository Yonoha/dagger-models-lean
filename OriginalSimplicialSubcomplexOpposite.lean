import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Reversing a simplicial subcomplex with the native simplicial opposite

The predicate is transported by the native degreewise equivalence, and its
closure uses the original subcomplex map for the reversed simplex operator.
This small generic construction avoids unfolding a particular core predicate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalSimplicialSubcomplexOpposite

noncomputable section

/-- Reverse a subcomplex using the exact native simplicial reversal. -/
def oppositeSubcomplex {X : SSet.{u}} (A : X.Subcomplex) : X.op.Subcomplex where
  obj q := {s | SSet.opObjEquiv s ∈ A.obj q}
  map f := by
    intro s hs
    change SSet.opObjEquiv (X.op.map f s) ∈ A.obj _
    rw [SSet.op_map]
    exact A.map (SimplexCategory.rev.map f.unop).op hs

/-- The underlying simplicial set is precisely the native opposite of the subcomplex. -/
theorem oppositeSubcomplex_toSSet {X : SSet.{u}} (A : X.Subcomplex) :
    (oppositeSubcomplex A : SSet.{u}) = (A : SSet.{u}).op := rfl

/-- The inclusion of the reversed subcomplex is the native opposite inclusion. -/
theorem oppositeSubcomplex_ι {X : SSet.{u}} (A : X.Subcomplex) :
    (oppositeSubcomplex A).ι = SSet.opFunctor.map A.ι := rfl


/-- Use Mathlib's range lift to land in the exact native opposite of a subcomplex. -/
def liftToOpposite {X Y : SSet.{u}} (A : X.Subcomplex) (f : Y ⟶ X.op)
    (hf : SSet.Subcomplex.range f ≤ oppositeSubcomplex A) : Y ⟶ (A : SSet.{u}).op :=
  SSet.Subcomplex.lift f hf

/-- The native range lift commutes with the exact opposite inclusion. -/
theorem liftToOpposite_comp_ι {X Y : SSet.{u}} (A : X.Subcomplex) (f : Y ⟶ X.op)
    (hf : SSet.Subcomplex.range f ≤ oppositeSubcomplex A) :
    liftToOpposite A f hf ≫ SSet.opFunctor.map A.ι = f :=
  SSet.Subcomplex.lift_ι f hf

/-- The range lift keeps the original underlying simplex under the native op equivalence. -/
theorem liftToOpposite_app_val {X Y : SSet.{u}} (A : X.Subcomplex) (f : Y ⟶ X.op)
    (hf : SSet.Subcomplex.range f ≤ oppositeSubcomplex A) (q : SimplexCategoryᵒᵖ)
    (s : Y.obj q) :
    (SSet.opObjEquiv ((liftToOpposite A f hf).app q s)).val =
      SSet.opObjEquiv (f.app q s) := rfl

/-- The exact native opposite inclusion is mono, by the reversed subcomplex inclusion. -/
theorem mono_op_inclusion {X : SSet.{u}} (A : X.Subcomplex) :
    Mono (SSet.opFunctor.map A.ι) := by
  change Mono (oppositeSubcomplex A).ι
  infer_instance

end

end DaggerOriginalSimplicialSubcomplexOpposite
