import NativeThickeningCotensorContraction

/-! The enriched full-path contraction has the SAME exact original endpoint functors. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerModels OrdinaryRigidification DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectCotensorPoints
open DaggerNativeThickeningCotensorContraction DaggerNativeThickeningFullPathHomotopy
open DaggerNativeThickeningFullSection DaggerActualOrdinalRigidificationComparison
universe u
namespace DaggerNativeThickeningContractionEndpoints
noncomputable section

/-- The exact same interval vertex used by the native homotopy inclusions. -/
def endpoint (e : Fin 2) : (𝟙_ SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  SSet.const (SSet.stdSimplex.obj₀Equiv.symm e)

/-- Native evaluation as an original enriched functor, with no object change. -/
def evaluationFunctor {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) : originalCotensor K C ⟶ C :=
  originalHom (evaluation a ⟨C.enriched⟩)

/-- Zero is the entire original identity enriched functor. -/
theorem zero (n : SimplexCategory) :
    contractionFunctor n ≫ evaluationFunctor (endpoint 0) (cosimplicialThickening.obj n) =
      𝟙 (cosimplicialThickening.obj n) := by
  apply EnrichedFunctor.ext SSet
    (F := contractionFunctor n ≫
      evaluationFunctor (endpoint 0) (cosimplicialThickening.obj n))
    (G := 𝟙 (cosimplicialThickening.obj n)) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext q p
  exact congrFun (NatTrans.congr_app (contraction_zero x.as y.as) q) p

/-- One is exactly the original projection followed by its full-path section. -/
theorem one (n : SimplexCategory) :
    contractionFunctor n ≫ evaluationFunctor (endpoint 1) (cosimplicialThickening.obj n) =
      thickeningProjection n.len ≫ fullSection n := by
  apply EnrichedFunctor.ext SSet
    (F := contractionFunctor n ≫
      evaluationFunctor (endpoint 1) (cosimplicialThickening.obj n))
    (G := thickeningProjection n.len ≫ fullSection n) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext q p
  exact (congrFun (NatTrans.congr_app (contraction_one x.as y.as) q) p).trans
    (CategoryTheory.Functor.ext (fun _ ↦ rfl))

end
end DaggerNativeThickeningContractionEndpoints
