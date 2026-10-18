import OriginalCoherentCotensorResolution
import NativeContractibleSimplexParameter
import NativeBisimplicialDiagonalWeak

/-! The original coherent-nerve constant leg is weak on every genuine simplex parameter. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra MonoidalCategory
open CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerNativeContractibleSimplexParameter DaggerNativeCoherentCotensorConstants
open DaggerOriginalCoherentCotensorResolution DaggerNativeBisimplicialDiagonal
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoherentCotensorResolutionWeak
noncomputable section

theorem simplex_parameter_GW (n : SimplexCategory) :
    DaggerSSetGluing.GW (toUnit (SSet.stdSimplex.obj n : SSet.{u})) := by
  induction n using SimplexCategory.rec with
  | _ n =>
    have : WeakEquivalence (snd (Δ[n] : SSet.{u}) (𝟙_ SSet.{u})) :=
      simplexProjection_weakEquivalence n _
    have h : (ρ_ (Δ[n] : SSet.{u})).inv ≫ snd (Δ[n] : SSet.{u}) (𝟙_ SSet.{u}) =
        toUnit (Δ[n] : SSet.{u}) := isTerminalTensorUnit.hom_ext _ _
    have hw : WeakEquivalence ((ρ_ (Δ[n] : SSet.{u})).inv ≫
        snd (Δ[n] : SSet.{u}) (𝟙_ SSet.{u})) := inferInstance
    rw [h] at hw
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1 hw

theorem constantComparison_app_weak (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hG : HasActualComponentGroupoid C) (n : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((constantComparison C).app n) :=
  constant_nerve_weak (SSet.stdSimplex.obj n.unop) C hC hG (simplex_parameter_GW n.unop)

/-- The actual full original coherent nerve maps weakly to its actual cotensor resolution. -/
theorem comparison_weak (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hG : HasActualComponentGroupoid C) : WeakEquivalence (comparison C) := by
  have : WeakEquivalence (diagonalFunctor.map (constantComparison C)) :=
    DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak (constantComparison C)
      (constantComparison_app_weak C hC hG)
  change WeakEquivalence ((diagonalConstantIso (coherentNerve.obj C)).inv ≫
    diagonalFunctor.map (constantComparison C))
  infer_instance

end
end DaggerNativeCoherentCotensorResolutionWeak
