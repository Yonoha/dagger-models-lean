import OriginalEnrichedCotensorMapping
import NativeCotensorParameterDiagonalNaturality

/-! An ORIGINAL enriched interval functor induces a homotopy on the FULL mapping SSet. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerOriginalEnrichedCotensorMapping
open DaggerOriginalCotensorPrecompositionWeak DaggerNativeCoherentCotensorConstants
open DaggerNativeOriginalCotensorFunctor DaggerNativeCotensorParameterDiagonal
open DaggerNativeCotensorParameterDiagonalNaturality
open DaggerNativeThickeningContractionEndpoints
universe u
namespace DaggerNativeOriginalMappingHomotopy
noncomputable section

/-- The actual Yoneda parameter respects every original simplex operator. -/
theorem yoneda_parameter {I : SSet.{u}} {q r : SimplexCategoryᵒᵖ} (a : q ⟶ r)
    (t : I.obj q) :
    (SSet.yonedaEquiv (X := I) (n := r.unop)).symm (I.map a t) =
      SSet.stdSimplex.map a.unop ≫ (SSet.yonedaEquiv (X := I) (n := q.unop)).symm t := by
  apply SSet.yonedaEquiv.injective
  simpa only [Equiv.apply_symm_apply] using
    (SSet.yonedaEquiv_map_comp a.unop
      ((SSet.yonedaEquiv (X := I) (n := q.unop)).symm t)).symm

/-- A global point gives the exact original constant parameter map. -/
theorem yoneda_point {I : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ I) (q : SimplexCategoryᵒᵖ) :
    (SSet.yonedaEquiv (X := I) (n := q.unop)).symm (a.app q PUnit.unit) =
      toUnit (SSet.stdSimplex.obj q.unop) ≫ a := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change a.app q PUnit.unit = a.app q
    ((toUnit (SSet.stdSimplex.obj q.unop)).app q (SSet.stdSimplex.objEquiv.symm (𝟙 q.unop)))
  apply congrArg (a.app q)
  change (PUnit.unit : PUnit.{u + 1}) = _
  exact Subsingleton.elim _ _

/-- No source simplex is restricted to an injective or fixed target-object function. -/
def homotopyMap {A : SimplicialCat.{u, u}}
    (H : A ⟶ originalCotensor (Δ[1] : SSet.{u}) A) (C : SimplicialCat.{u, u}) :
    mapping A C ⊗ (Δ[1] : SSet.{u}) ⟶ mapping A C where
  app q z := ⟨H ≫ map (Δ[1] : SSet.{u}) z.1.down ≫ evaluationAlong
    ((SSet.yonedaEquiv (X := (Δ[1] : SSet.{u})) (n := q.unop)).symm z.2) C⟩
  naturality q r a := by
    funext z
    apply ULift.ext
    change H ≫ map (Δ[1] : SSet.{u})
      (z.1.down ≫ restrictionFunctor (SSet.stdSimplex.map a.unop) C) ≫ evaluationAlong
        ((SSet.yonedaEquiv (X := (Δ[1] : SSet.{u})) (n := r.unop)).symm
          ((Δ[1] : SSet.{u}).map a z.2)) C =
      (H ≫ map (Δ[1] : SSet.{u}) z.1.down ≫ evaluationAlong
        ((SSet.yonedaEquiv (X := (Δ[1] : SSet.{u})) (n := q.unop)).symm z.2) C) ≫
          restrictionFunctor (SSet.stdSimplex.map a.unop) C
    rw [DaggerNativeOriginalCotensorFunctor.map_comp, yoneda_parameter]
    simp only [Category.assoc]
    rw [DaggerNativeCotensorParameterDiagonalNaturality.parameter_naturality]

/-- At every original global interval point the whole functor is exact precomposition. -/
theorem homotopyMap_point {A : SimplicialCat.{u, u}}
    (H : A ⟶ originalCotensor (Δ[1] : SSet.{u}) A) (C : SimplicialCat.{u, u})
    (a : 𝟙_ SSet.{u} ⟶ (Δ[1] : SSet.{u})) (q : SimplexCategoryᵒᵖ)
    (F : (mapping A C).obj q) :
    (homotopyMap H C).app q (F, a.app q PUnit.unit) =
      ⟨(H ≫ evaluationFunctor a A) ≫ F.down⟩ := by
  apply ULift.ext
  change H ≫ map (Δ[1] : SSet.{u}) F.down ≫ evaluationAlong
    ((SSet.yonedaEquiv (X := (Δ[1] : SSet.{u})) (n := q.unop)).symm
      (a.app q PUnit.unit)) C = (H ≫ evaluationFunctor a A) ≫ F.down
  rw [yoneda_point, DaggerNativeCotensorParameterDiagonalNaturality.constant_parameter,
    evaluation_naturality, Category.assoc]

/-- Both endpoints are maps of the entire original mapping SSet. -/
def homotopy {A : SimplicialCat.{u, u}}
    (H : A ⟶ originalCotensor (Δ[1] : SSet.{u}) A) (C : SimplicialCat.{u, u}) :
    SSet.Homotopy (pre (H ≫ evaluationFunctor (endpoint 0) A) C)
      (pre (H ≫ evaluationFunctor (endpoint 1) A) C) :=
  SSet.Homotopy.mk (homotopyMap H C) (by
    apply NatTrans.ext
    funext q F
    exact homotopyMap_point H C (endpoint 0) q F) (by
    apply NatTrans.ext
    funext q F
    exact homotopyMap_point H C (endpoint 1) q F)

end
end DaggerNativeOriginalMappingHomotopy
