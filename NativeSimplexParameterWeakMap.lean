import NativeContractibleSimplexParameter

/-!
# Native weak equivalences of maps with a standard-simplex parameter

Weakness on the exact native first-vertex section implies weakness of the full
parameterized map. The cartesian lift retaining the entire parameter is weak
as well. The statements quantify over all original target simplicial sets.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open DaggerNativeStandardSimplexContraction DaggerNativeContractibleSimplexParameter
universe u
namespace DaggerNativeSimplexParameterWeakMap
noncomputable section

/-- Weakness at the first vertex implies weakness of the exact map on the full parameter. -/
theorem parameterizedMap_weakEquivalence (n : ℕ) (Y Z : SSet.{u})
    (f : (Δ[n] : SSet.{u}) ⊗ Y ⟶ Z)
    (hf : WeakEquivalence (pointSection (simplexContractible n) Y ≫ f)) :
    WeakEquivalence f := by
  have : WeakEquivalence (pointSection (simplexContractible n) Y) :=
    pointSection_weakEquivalence (simplexContractible n) Y
  have : WeakEquivalence (pointSection (simplexContractible n) Y ≫ f) := hf
  exact weakEquivalence_of_precomp_of_fac
    (f := pointSection (simplexContractible n) Y) (g := f)
    (fg := pointSection (simplexContractible n) Y ≫ f) rfl

/-- Keeping the identical parameter coordinate also gives an actual native weak equivalence. -/
theorem relativeParameterizedMap_weakEquivalence (n : ℕ) (Y Z : SSet.{u})
    (f : (Δ[n] : SSet.{u}) ⊗ Y ⟶ Z)
    (hf : WeakEquivalence (pointSection (simplexContractible n) Y ≫ f)) :
    WeakEquivalence (lift (fst (Δ[n] : SSet.{u}) Y) f) := by
  have : WeakEquivalence f := parameterizedMap_weakEquivalence n Y Z f hf
  have : WeakEquivalence (snd (Δ[n] : SSet.{u}) Z) :=
    simplexProjection_weakEquivalence n Z
  apply weakEquivalence_of_postcomp_of_fac
    (f := lift (fst (Δ[n] : SSet.{u}) Y) f) (g := snd (Δ[n] : SSet.{u}) Z) (fg := f)
  apply NatTrans.ext
  funext d p
  rfl

end
end DaggerNativeSimplexParameterWeakMap
