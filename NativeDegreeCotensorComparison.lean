import NativeDegreeCotensorYoneda
import OriginalCoherentCotensorResolution

/-! The actual ordinary-nerve map into the same coherent cotensor resolution. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialDegreeCategory DaggerActualConstantEnrichmentFunctor
open DaggerNativeDegreeCotensorYoneda DaggerNativeCoherentCotensorConstants
open DaggerOriginalCoherentCotensorResolution DaggerOriginalSimplicialCategoryDiagonalNerve
universe u
namespace DaggerNativeDegreeCotensorComparison
noncomputable section

local instance (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    EnrichedCategory SSet.{u} (degreeObjects C n) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

/-- The entire Yoneda comparison respects every parameter operator. -/
theorem parameter_naturality (C : SimplicialCat.{u, u})
    {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) :
    constantMap (degreeMap C a) ≫ degreeToCotensor C m.unop =
      degreeToCotensor C n.unop ≫ restrictionFunctor (SSet.stdSimplex.map a.unop) C := by
  apply EnrichedFunctor.ext SSet
    (F := constantMap (degreeMap C a) ≫ degreeToCotensor C m.unop)
    (G := degreeToCotensor C n.unop ≫ restrictionFunctor (SSet.stdSimplex.map a.unop) C)
    (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext q f
  apply Functor.HomObj.ext
  funext r i k
  change (C.enriched.Hom x y).map (SSet.stdSimplex.objEquiv k).op
    ((C.enriched.Hom x y).map a f) =
      (C.enriched.Hom x y).map ((SSet.stdSimplex.objEquiv k ≫ a.unop).op) f
  exact (congrFun ((C.enriched.Hom x y).map_comp a
    (SSet.stdSimplex.objEquiv k).op) f).symm

/-- The same Yoneda map respects all original enriched functors and their object maps. -/
theorem functor_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) :
    constantMap (degreeFunctor F n) ≫ degreeToCotensor D n.unop =
      degreeToCotensor C n.unop ≫
        DaggerNativeOriginalCotensorFunctor.map (SSet.stdSimplex.obj n.unop) F := by
  apply EnrichedFunctor.ext SSet
    (F := constantMap (degreeFunctor F n) ≫ degreeToCotensor D n.unop)
    (G := degreeToCotensor C n.unop ≫
      DaggerNativeOriginalCotensorFunctor.map (SSet.stdSimplex.obj n.unop) F) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext q f
  apply Functor.HomObj.ext
  funext r i k
  exact (congrFun ((F.map x y).naturality (SSet.stdSimplex.objEquiv k).op) f).symm

/-- The full bisimplicial map is defined; its row weak-equivalence theorem is separate. -/
def comparison (C : SimplicialCat.{u, u}) :
    bisimplicialNerveFunctor.obj C ⟶ resolution C where
  app n := (DaggerActualConstantCoherentNerve.coherentNerveIso (degreeObjects C n)).inv ≫
    coherentNerve.map (degreeToCotensor C n.unop)
  naturality n m a := by
    change nerveMap (degreeMap C a) ≫ (_ ≫ _) = (_ ≫ _) ≫ coherentNerve.map _
    rw [← Category.assoc, ← inverse_naturality (degreeMap C a), Category.assoc,
      ← coherentNerve.map_comp, parameter_naturality]
    rw [coherentNerve.map_comp, Category.assoc]
    rfl

end
end DaggerNativeDegreeCotensorComparison
