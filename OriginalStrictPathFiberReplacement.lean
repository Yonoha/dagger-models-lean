import OriginalFullVertexPathFiberModelConsequences
import SSetRightProper

/-!
# The actual strict fiber compared with a specified weak point replacement

This reuses the retained right-properness theorem and the native pullback
description of the literal simplicial fiber. It avoids the older full-vertex
implementation. The replacement, both legs and their equality with the
original endpoint point are explicit. No choice-independent derived mapping
space or equivariant derived recognition is assumed.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial Opposite
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalStrictPathFiberReplacement

variable {X Y R : SSet.{u}}
variable (f : X ⟶ Y) (y : Y.obj (op ⦋0⦌))
variable (i : (Δ[0] : SSet.{u}) ⟶ R) (p : R ⟶ Y)
variable (hpoint : i ≫ p = SSet.yonedaEquiv.symm y)

/-- The original fiber maps into the pullback along the actual supplied replacement. -/
noncomputable def comparison :
    (SSet.Subcomplex.fiber f y : SSet.{u}) ⟶ pullback f p :=
  pullback.lift (SSet.Subcomplex.fiber f y).ι
    (SSet.stdSimplex.objZeroIsTerminal.from _ ≫ i) (by
      rw [Category.assoc, hpoint]
      exact (SSet.Subcomplex.fiber_isPullback f y).w)

/-- The original fiber inclusion is exactly the first leg of the comparison. -/
theorem comparison_fst :
    comparison f y i p hpoint ≫ pullback.fst f p =
      (SSet.Subcomplex.fiber f y).ι := by
  simp [comparison]

/-- The second leg retains the same original point and replacement map. -/
theorem comparison_snd :
    comparison f y i p hpoint ≫ pullback.snd f p =
      SSet.stdSimplex.objZeroIsTerminal.from _ ≫ i := by
  simp [comparison]

/-- The comparison is literally the base change of the supplied weak point map. -/
theorem comparison_isPullback :
    IsPullback (comparison f y i p hpoint)
      (SSet.stdSimplex.objZeroIsTerminal.from _)
      (pullback.snd f p) i := by
  have outer : IsPullback
      (comparison f y i p hpoint ≫ pullback.fst f p)
      (SSet.stdSimplex.objZeroIsTerminal.from _) f (i ≫ p) := by
    simpa only [comparison_fst, hpoint] using SSet.Subcomplex.fiber_isPullback f y
  exact IsPullback.of_right outer (comparison_snd f y i p hpoint)
    (IsPullback.of_hasPullback f p)

/-- Native right properness proves weakness of this actual comparison map. -/
theorem comparison_weakEquivalence [Fibration f] [WeakEquivalence i] :
    WeakEquivalence (comparison f y i p hpoint) := by
  have : Fibration (pullback.snd f p) := inferInstance
  exact DaggerSSetRightProper.weakEquivalence_of_isPullback
    (comparison_isPullback f y i p hpoint)

variable {X' Y' R' : SSet.{u}}
variable (f' : X' ⟶ Y') (y' : Y'.obj (op ⦋0⦌))
variable (i' : (Δ[0] : SSet.{u}) ⟶ R') (p' : R' ⟶ Y')
variable (hpoint' : i' ≫ p' = SSet.yonedaEquiv.symm y')
variable (h : X ⟶ X') (k : Y ⟶ Y') (r : R ⟶ R')
variable (sq : f ≫ k = h ≫ f') (hr : p ≫ k = r ≫ p') (hi : i ≫ r = i')
variable (s : (SSet.Subcomplex.fiber f y : SSet.{u}) ⟶
  (SSet.Subcomplex.fiber f' y' : SSet.{u}))
variable (hs : s ≫ (SSet.Subcomplex.fiber f' y').ι =
  (SSet.Subcomplex.fiber f y).ι ≫ h)

include hi hs in
/-- Both literal comparison legs commute with a compatible original fiber map. -/
theorem comparison_naturality :
    comparison f y i p hpoint ≫ pullback.map f p f' p' h r k sq hr =
      s ≫ comparison f' y' i' p' hpoint' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst, comparison_fst]
    rw [← Category.assoc, comparison_fst]
    exact hs.symm
  · simp only [Category.assoc, pullback.map, pullback.lift_snd, comparison_snd]
    rw [← Category.assoc, comparison_snd, Category.assoc, hi, ← Category.assoc]
    congr 1

end DaggerOriginalStrictPathFiberReplacement
