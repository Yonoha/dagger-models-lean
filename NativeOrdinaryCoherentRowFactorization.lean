import NativeOrdinaryNerveRowIso
import NativeThickeningMappingWeak
import NativeDegreeCotensorComparison

/-!
Factor the SAME original ordinary/coherent row map through original projection precomposition.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalCoherentCotensorResolution DaggerOriginalEnrichedCotensorMapping
open DaggerActualConstantEnrichmentFunctor DaggerActualOrdinalRigidificationComparison
open DaggerNativeOrdinaryNerveRowIso
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOrdinaryCoherentRowFactorization
noncomputable section

local instance (C : SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ) :
    EnrichedCategory SSet.{u} (degreeObjects C q) := DaggerUnitaryDiscrete.ordinaryEnriched _

/-- The ENTIRE existing coherent chain is the original projection followed by its lifted chain. -/
theorem chain_projection (C : SimplicialCat.{u, u}) (q : SimplexCategoryᵒᵖ)
    (n : SimplexCategory) (p : (nerve (degreeObjects C q)).obj (op n)) :
    DaggerActualConstantCoherentSimplexComparison.fromOrdinary (degreeObjects C q) n p =
      thickeningProjection n.len ≫ constantMap ((ordinalEquivalence.{u} n).functor ⋙ p) := by
  apply EnrichedFunctor.ext SSet
    (F := DaggerActualConstantCoherentSimplexComparison.fromOrdinary (degreeObjects C q) n p)
    (G := thickeningProjection n.len ≫ constantMap ((ordinalEquivalence.{u} n).functor ⋙ p))
    (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext d g
  rfl

/-- The SAME actual coherent-nerve resolution row is the full original mapping SSet. -/
def resolutionRowIso (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    (resolution C).flip.obj (op n) ≅ mapping (cosimplicialThickening.obj n) C :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- Restrict the already constructed original comparison to its actual flipped row. -/
def rowComparison (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    nerveRow C n ⟶ (resolution C).flip.obj (op n) :=
  ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map
    (DaggerNativeDegreeCotensorComparison.comparison C)).app (op n)

/-- A WHOLE map equality, preserving all original simplices and repeated object labels. -/
theorem factorization (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    rowComparison C n ≫ (resolutionRowIso C n).hom =
      (DaggerNativeOrdinaryNerveRowIso.rowIso C n).hom ≫
        (DaggerNativeConstantSourceMappingRow.rowIso (ULift.{u} (Fin (n.len + 1))) C).hom ≫
          pre (thickeningProjection n.len) C := by
  apply NatTrans.ext
  funext q p
  apply ULift.ext
  change DaggerActualConstantCoherentSimplexComparison.fromOrdinary (degreeObjects C q) n p ≫
    DaggerNativeDegreeCotensorYoneda.degreeToCotensor C q.unop =
      thickeningProjection n.len ≫ (constantMap ((ordinalEquivalence.{u} n).functor ⋙ p) ≫
        DaggerNativeDegreeCotensorYoneda.degreeToCotensor C q.unop)
  rw [chain_projection, Category.assoc]

/-- The actual ORIGINAL comparison row is weak for every original target C. -/
theorem rowComparison_weak (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    WeakEquivalence (rowComparison C n) := by
  have : WeakEquivalence (pre (thickeningProjection.{u} n.len) C) :=
    DaggerNativeThickeningMappingWeak.projection_pre_weak n C
  have : WeakEquivalence (rowComparison C n ≫ (resolutionRowIso C n).hom) := by
    rw [factorization]
    infer_instance
  exact weakEquivalence_of_postcomp (rowComparison C n) (resolutionRowIso C n).hom

end
end DaggerNativeOrdinaryCoherentRowFactorization
