import OriginalNerveOppositeMap

/-!
# The native homotopy-category comparison for simplicial reversal

Transpose a concrete map into an opposite-category nerve through Mathlib's
actual nerve adjunction. Its degree-one formula proves that invertibility under
the original unit is preserved by simplicial reversal in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalNerveOppositeMap

universe v u

namespace DaggerOriginalHomotopyCategoryOppositeComparison

noncomputable section

/-- Reversal sends the literal degree-one arrow to its categorical opposite. -/
theorem reverseDiagram_hom {C : Type u} [Category.{v} C] (s : ComposableArrows C 1) :
    (reverseDiagram s).hom = s.hom.op := rfl

/-- Reverse the native unit of X.op, then compare with the opposite-category nerve. -/
def unitOppositeComparison (X : SSet.{u}) :
    X ⟶ nerve (SSet.hoFunctor.obj X.op)ᵒᵖ :=
  SSet.opFunctorCompOpFunctorIso.inv.app X ≫
    SSet.opFunctor.map (homotopyCategoryUnit X.op) ≫
      nerveOppositeMap (SSet.hoFunctor.obj X.op)

/-- The exact comparison functor obtained by the native nerve adjunction. -/
def hoOppositeComparison (X : SSet.{u}) :
    SSet.hoFunctor.obj X ⥤ (SSet.hoFunctor.obj X.op)ᵒᵖ :=
  ((nerveAdjunction.homEquiv X (Cat.of (SSet.hoFunctor.obj X.op)ᵒᵖ)).symm
    (unitOppositeComparison X)).toFunctor

/-- The comparison satisfies the exact unit equation in every simplicial degree. -/
theorem unit_comp_nerve_hoOppositeComparison (X : SSet.{u}) :
    homotopyCategoryUnit X ≫ nerveMap (hoOppositeComparison X) =
      unitOppositeComparison X := by
  have h := (nerveAdjunction.homEquiv X (Cat.of (SSet.hoFunctor.obj X.op)ᵒᵖ)).apply_symm_apply
    (unitOppositeComparison X)
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- The unit comparison on a degree-one simplex is the opposite of the exact reversed edge. -/
theorem unitOppositeComparison_app_one (X : SSet.{u}) (e : X.obj (op ⦋1⦌)) :
    ((unitOppositeComparison X).app (op ⦋1⦌) e).hom =
      (((homotopyCategoryUnit X.op).app (op ⦋1⦌) (SSet.opObjEquiv.symm e)).hom).op := by
  change (reverseDiagram ((homotopyCategoryUnit X.op).app (op ⦋1⦌)
    (SSet.opObjEquiv.symm e))).hom = _
  exact reverseDiagram_hom _

/-- Simplicial reversal preserves invertibility for the original homotopy-category unit. -/
theorem edgeIsInvertible_op (X : SSet.{u}) (e : X.obj (op ⦋1⦌))
    (he : edgeIsInvertible X e) : edgeIsInvertible X.op (SSet.opObjEquiv.symm e) := by
  have : IsIso (((homotopyCategoryUnit X).app (op ⦋1⦌) e).hom) := he
  have hf : IsIso ((hoOppositeComparison X).map
      (((homotopyCategoryUnit X).app (op ⦋1⦌) e).hom)) := inferInstance
  change IsIso (((nerveMap (hoOppositeComparison X)).app (op ⦋1⦌)
    ((homotopyCategoryUnit X).app (op ⦋1⦌) e)).hom) at hf
  have hn := congrArg
    (fun k : X ⟶ nerve (SSet.hoFunctor.obj X.op)ᵒᵖ ↦ k.app (op ⦋1⦌) e)
    (unit_comp_nerve_hoOppositeComparison X)
  change (nerveMap (hoOppositeComparison X)).app (op ⦋1⦌)
    ((homotopyCategoryUnit X).app (op ⦋1⦌) e) =
      (unitOppositeComparison X).app (op ⦋1⦌) e at hn
  rw [hn, unitOppositeComparison_app_one] at hf
  exact (isIso_op_iff _).mp hf

end

end DaggerOriginalHomotopyCategoryOppositeComparison
