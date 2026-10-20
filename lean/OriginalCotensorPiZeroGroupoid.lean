import OriginalCotensorPrecompositionWeak
import OriginalPiZeroGroupoidFromWeakPrecomposition
import OriginalPiZeroBarProjectionFibration

/-! Every original cotensor of a locally Kan pi0 groupoid again has its exact pi0 groupoid. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalPiZeroGroupoidFromWeakPrecomposition
open DaggerOriginalNerveRowsPiZero DaggerOriginalBarRowsPiZero
open DaggerOriginalPiZeroNerveRowsKan DaggerOriginalPiZeroBarRowsKan
open DaggerOriginalPiZeroBarProjectionFibration DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalCotensorPiZeroGroupoid
noncomputable section

theorem cotensor_groupoid (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) :
    HasActualComponentGroupoid (originalCotensor K C) := by
  apply groupoid_of_weak_precomposition
  intro x y a z
  have := hH y z
  have := hH x z
  exact cotensor_precompose_weak K C hC a z

theorem replacement_cotensor_groupoid (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    HasActualComponentGroupoid (originalCotensor K (replacement.obj C)) :=
  cotensor_groupoid K (replacement.obj C) ((replacement_groupoid_iff C).mp hC)
    (replacement_locallyKan C)

theorem cotensor_base_rows_kan (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) :
    (componentRows (originalCotensor K C)).KanComplex :=
  componentRows_kan _ (cotensor_groupoid K C hC hH)

theorem cotensor_bar_rows_kan (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) (z : C.Obj) :
    (barComponentRows (originalCotensor K C) z).KanComplex :=
  barComponentRows_kan _ (cotensor_groupoid K C hC hH) z

theorem cotensor_pi_zero_projection_fibration (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) (z : C.Obj) :
    Fibration (componentRowProjection (originalCotensor K C) z) :=
  component_projection_fibration _ (cotensor_groupoid K C hC hH) z

theorem replacement_cotensor_pi_zero_descent_inputs (K : SSet.{u})
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    (componentRows (originalCotensor K (replacement.obj C))).KanComplex ∧
      ∀ z : (replacement.obj C).Obj,
        (barComponentRows (originalCotensor K (replacement.obj C)) z).KanComplex ∧
          Fibration (componentRowProjection (originalCotensor K (replacement.obj C)) z) := by
  have h := replacement_cotensor_groupoid K C hC
  exact ⟨componentRows_kan _ h, fun z ↦
    ⟨barComponentRows_kan _ h z, component_projection_fibration _ h z⟩⟩

end
end DaggerOriginalCotensorPiZeroGroupoid
