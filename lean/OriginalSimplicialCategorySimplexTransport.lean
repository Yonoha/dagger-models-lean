import NativeContractibleSimplexParameter

/-!
# Original Hom simplices act by parameterized original precomposition

An arbitrary original Hom n-simplex is represented by its native Yoneda map.
Composition acts on the full product with the original target Hom. The relative
map retains exactly the same standard-simplex parameter. Restriction to the
native first vertex is the already established original vertex transport.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial DaggerModels
open DaggerNativeStandardSimplexContraction DaggerNativeContractibleSimplexParameter
open DaggerOriginalSimplicialCategoryVertexComposition
universe u
namespace DaggerOriginalSimplicialCategorySimplexTransport
noncomputable section

/-- The first vertex of the exact original Hom simplex, via its native Yoneda map. -/
def simplexFirstVertex (C : SimplicialCat.{u, u}) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) : (C.enriched.Hom x y).obj (op ⦋0⦌) :=
  (SSet.yonedaEquiv.symm σ).app (op ⦋0⦌) (firstVertex n)

/-- The original simplex supplies actual enriched precomposition on the full target Hom. -/
def simplexPrecompose (C : SimplicialCat.{u, u}) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) (z : C.Obj) :
    (Δ[n] : SSet.{u}) ⊗ C.enriched.Hom y z ⟶ C.enriched.Hom x z :=
  (SSet.yonedaEquiv.symm σ ⊗ₘ 𝟙 (C.enriched.Hom y z)) ≫ C.enriched.comp x y z

/-- Retain the exact original simplex parameter while applying original composition. -/
def relativeSimplexPrecompose (C : SimplicialCat.{u, u}) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) (z : C.Obj) :
    (Δ[n] : SSet.{u}) ⊗ C.enriched.Hom y z ⟶ (Δ[n] : SSet.{u}) ⊗ C.enriched.Hom x z :=
  lift (fst _ _) (simplexPrecompose C σ z)

/-- All parameterized values are the exact original enriched composition values. -/
theorem simplexPrecompose_apply (C : SimplicialCat.{u, u}) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) (z : C.Obj) (d : SimplexCategoryᵒᵖ)
    (t : (Δ[n] : SSet.{u}).obj d) (b : (C.enriched.Hom y z).obj d) :
    (simplexPrecompose C σ z).app d (t, b) =
      (C.enriched.comp x y z).app d ((SSet.yonedaEquiv.symm σ).app d t, b) := rfl

/-- The relative map keeps its exact original parameter coordinate. -/
theorem relativeSimplexPrecompose_fst (C : SimplicialCat.{u, u}) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) (z : C.Obj) :
    relativeSimplexPrecompose C σ z ≫ fst _ _ = fst _ _ := by
  apply NatTrans.ext
  funext d p
  rfl

/-- Its second coordinate is precisely the original parameterized precomposition. -/
theorem relativeSimplexPrecompose_snd (C : SimplicialCat.{u, u}) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) (z : C.Obj) :
    relativeSimplexPrecompose C σ z ≫ snd _ _ = simplexPrecompose C σ z := by
  apply NatTrans.ext
  funext d p
  rfl

/-- Restriction at the native first vertex is the exact original vertex precomposition. -/
theorem simplexPrecompose_firstVertex (C : SimplicialCat.{u, u}) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) (z : C.Obj) :
    pointSection (simplexContractible n) (C.enriched.Hom y z) ≫ simplexPrecompose C σ z =
      precomposeVertex C (simplexFirstVertex C σ) z := by
  have hp : SSet.const (X := 𝟙_ SSet.{u}) (firstVertex n) ≫
      SSet.yonedaEquiv.symm σ = vertexPoint C (simplexFirstVertex C σ) := by
    apply (SSet.unitHomEquiv (C.enriched.Hom x y)).injective
    simp only [vertexPoint, Equiv.apply_symm_apply]
    change (SSet.yonedaEquiv.symm σ).app (op ⦋0⦌)
      ((SSet.const (X := 𝟙_ SSet.{u}) (firstVertex n)).app (op ⦋0⦌) PUnit.unit) = _
    have hid : (⦋0⦌.const ⦋0⦌ 0) = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    simpa only [SSet.const_app, hid, op_id, FunctorToTypes.map_id_apply] using
      (show (SSet.yonedaEquiv.symm σ).app (op ⦋0⦌) (firstVertex n) =
        simplexFirstVertex C σ from rfl)
  apply NatTrans.ext
  funext d b
  change (C.enriched.comp x y z).app d
      ((SSet.const (X := 𝟙_ SSet.{u}) (firstVertex n) ≫
        SSet.yonedaEquiv.symm σ).app d PUnit.unit, b) =
    (C.enriched.comp x y z).app d ((vertexPoint C (simplexFirstVertex C σ)).app d
      PUnit.unit, b)
  rw [hp]

end
end DaggerOriginalSimplicialCategorySimplexTransport
