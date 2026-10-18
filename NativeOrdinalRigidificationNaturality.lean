import ActualOrdinalRigidificationComparison
import ActualConstantEnrichmentFunctor

/-! The existing original rigidified-simplex projection is natural under every operator. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualConstantEnrichmentFunctor
open DaggerActualOrdinalRigidificationComparison
universe u
namespace DaggerNativeOrdinalRigidificationNaturality
noncomputable section

/-- The actual lifted finite ordinal used by the native thickening. -/
abbrev ordinal (n : SimplexCategory) := ULift.{u} (Fin (n.len + 1))

local instance (n : SimplexCategory) : EnrichedCategory SSet.{u} (ordinal n) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

/-- The original simplex operator on its actual lifted objects. -/
def ordinalMap {n m : SimplexCategory} (a : n ⟶ m) : ordinal.{u} n ⥤ ordinal.{u} m where
  obj x := ⟨a.toOrderHom x.down⟩
  map {x y} f := by
    have h : x ≤ y := leOfHom f
    apply homOfLE
    exact a.toOrderHom.monotone h

/-- No injectivity condition is imposed on the simplex operator. -/
theorem thickeningProjection_naturality {n m : SimplexCategory} (a : n ⟶ m) :
    cosimplicialThickening.map a ≫ thickeningProjection m.len =
      thickeningProjection n.len ≫ constantMap (ordinalMap.{u} a) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

/-- The SAME original rigidified-simplex projection, for any native simplex object. -/
def projection (n : SimplexCategory) :
    rigidification.obj (SSet.stdSimplex.obj n) ⟶ constant (ordinal.{u} n) :=
  (rigidificationSimplexIso.hom.app n) ≫ thickeningProjection n.len

/-- Naturality of the whole original enriched projection, including degenerate operators. -/
theorem projection_naturality {n m : SimplexCategory} (a : n ⟶ m) :
    rigidification.map (SSet.stdSimplex.map a) ≫ projection m =
      projection n ≫ constantMap (ordinalMap.{u} a) := by
  unfold projection
  have h := rigidificationSimplexIso.hom.naturality a
  change rigidification.map (SSet.stdSimplex.map a) ≫
    rigidificationSimplexIso.hom.app m =
      rigidificationSimplexIso.hom.app n ≫ cosimplicialThickening.map a at h
  rw [← Category.assoc, h,
    Category.assoc, thickeningProjection_naturality, ← Category.assoc]

/-- The map is literally the previously verified comparison, with no replacement. -/
theorem projection_eq_original (n : ℕ) :
    projection.{u} ⦋n⦌ = DaggerActualOrdinalRigidificationComparison.comparison n := rfl

end
end DaggerNativeOrdinalRigidificationNaturality
