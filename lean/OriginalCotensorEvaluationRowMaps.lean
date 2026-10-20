import OriginalConnectedMappingRowPiZero
import OriginalCotensorEvaluationNerveFibration

/-! Original point evaluation on full row diagrams agrees with the original enriched functor. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory MonoidalClosed DaggerModels
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalNerveRowChainData DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryOverDiagram DaggerOriginalFixedObjectCotensorPoints
open DaggerOriginalConnectedCotensorBaseRows DaggerOriginalConnectedCotensorBarRows
open DaggerOriginalNerveRowsPiZero DaggerOriginalBarRowsPiZero
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalCotensorEvaluationNerveFibration
universe u
namespace DaggerOriginalCotensorEvaluationRowMaps
noncomputable section

def baseRowsEvaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) (C : SimplicialCat.{u, u}) :
    baseRows C ⋙ ihom K ⟶ baseRows C where
  app n := pointEvaluation a (baseRow C n.unop.len)
  naturality _ _ α := pointEvaluation_natural a ((baseRows C).map α)

def barRowsEvaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) (C : SimplicialCat.{u, u})
    (z : C.Obj) : barRows C z ⋙ ihom K ⟶ barRows C z where
  app n := pointEvaluation a (barRow C z n.unop.len)
  naturality _ _ α := pointEvaluation_natural a ((barRows C z).map α)

def barRowsMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (z : C.Obj) :
    barRows C z ⟶ barRows D (F.obj z) :=
  (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map
    (Functor.whiskerRight (overCategoryMap F z) nerveFunctor)

def barComponentRowsMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (z : C.Obj) :
    barComponentRows C z ⟶ barComponentRows D (F.obj z) :=
  Functor.whiskerRight (barRowsMap F z) SSet.π₀Functor

theorem barComponentsIso_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (z : C.Obj) :
    barComponentRowsMap F z ≫ (barComponentRowsIso D (F.obj z)).hom =
      (barComponentRowsIso C z).hom ≫ nerveMap (Over.post (componentFunctor F)) := by
  apply NatTrans.ext
  funext n q
  obtain ⟨B, rfl⟩ := SSet.π₀.mk_surjective q
  change barRowComponentsEquiv D (F.obj z) n.unop.len
      (SSet.mapπ₀ ((barRowsMap F z).app n) (SSet.π₀.mk B)) =
    (nerveMap (Over.post (componentFunctor F))).app n
      (barRowComponentsEquiv C z n.unop.len (SSet.π₀.mk B))
  rw [SSet.mapπ₀_mk, barRowComponentsEquiv_mk, barRowComponentsEquiv_mk]
  rfl

theorem base_row_evaluation_eq {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) (k : ℕ) :
    baseRowIhomMap K C k ≫ pointEvaluation a (baseRow C k) =
      (baseRowsMap (evaluationFunctor a C)).app (op ⦋k⦌) := by
  apply NatTrans.ext
  rfl

theorem bar_row_evaluation_eq {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) :
    barRowIhomMap K C z k ≫ pointEvaluation a (barRow C z k) =
      (barRowsMap (evaluationFunctor a C) z).app (op ⦋k⦌) := by
  apply NatTrans.ext
  rfl

end
end DaggerOriginalCotensorEvaluationRowMaps
