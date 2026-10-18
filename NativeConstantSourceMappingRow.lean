import NativeConstantCotensorFunctorEquiv
import NativeDegreeCotensorComparison
import OriginalEnrichedCotensorMapping

/-! The SAME original constant-source mapping SSet has the full degree-functor row. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerActualConstantSimplicialCategory
open DaggerActualConstantEnrichmentFunctor DaggerNativeConstantCotensorFunctorEquiv
open DaggerOriginalEnrichedCotensorMapping
universe u
namespace DaggerNativeConstantSourceMappingRow
noncomputable section
variable (A : Type u) [Category.{u} A]
local instance : EnrichedCategory SSet.{u} A := DaggerUnitaryDiscrete.ordinaryEnriched _

/-- Keep ALL original ordinary functors from A in each actual degree category. -/
def ordinaryRow (C : SimplicialCat.{u, u}) : SSet.{u} where
  obj q := ULift (A ⥤ degreeObjects C q)
  map a F := ⟨F.down ⋙ degreeMap C a⟩
  map_id q := by
    funext F
    apply ULift.ext
    change F.down ⋙ degreeMap C (𝟙 q) = F.down
    rw [degreeMap_id, CategoryTheory.Functor.comp_id]
  map_comp a b := by
    funext F
    apply ULift.ext
    change F.down ⋙ degreeMap C (a ≫ b) = (F.down ⋙ degreeMap C a) ⋙ degreeMap C b
    rw [degreeMap_comp]
    exact (CategoryTheory.Functor.assoc F.down _ _).symm

/-- The actual degreeToCotensor map, retaining the original entire object function. -/
def comparison (C : SimplicialCat.{u, u}) : ordinaryRow A C ⟶ mapping (constant A) C where
  app q F := ⟨fromOrdinary A C q F.down⟩
  naturality n m a := by
    funext F
    apply ULift.ext
    change fromOrdinary A C m (F.down ⋙ degreeMap C a) =
      fromOrdinary A C n F.down ≫
        DaggerNativeCoherentCotensorConstants.restrictionFunctor (SSet.stdSimplex.map a.unop) C
    have h : constantMap (F.down ⋙ degreeMap C a) =
        constantMap F.down ≫ constantMap (degreeMap C a) :=
      DaggerActualConstantEnrichmentFunctor.constantFunctor.map_comp
        F.down.toCatHom (degreeMap C a).toCatHom
    unfold fromOrdinary
    rw [h, Category.assoc, DaggerNativeDegreeCotensorComparison.parameter_naturality,
      ← Category.assoc]

/-- Both whole-functor inverse identities assemble to an actual original SSet isomorphism. -/
def rowIso (C : SimplicialCat.{u, u}) : ordinaryRow A C ≅ mapping (constant A) C :=
  NatIso.ofComponents (fun q ↦
    (Equiv.ulift.trans ((functorEquiv A C q).symm.trans Equiv.ulift.symm)).toIso)
    (fun a ↦ (comparison A C).naturality a)

/-- Its entire forward map is the already specified original comparison. -/
theorem rowIso_hom (C : SimplicialCat.{u, u}) : (rowIso A C).hom = comparison A C := by
  apply NatTrans.ext
  funext q F
  rfl

end
end DaggerNativeConstantSourceMappingRow
