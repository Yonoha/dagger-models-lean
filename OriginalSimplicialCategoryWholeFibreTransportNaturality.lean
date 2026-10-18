import OriginalSimplicialCategoryWholeTransportNaturality
import OriginalSimplicialCategoryWholeBarFibreLocalization

/-!
# Whole original strict-fibre transport commutes with the actual localization

First prove naturality for every original enriched functor, retaining every
original object and Hom map. Then specialize to the actual original completion
unit, whose Hom maps are the actual localizationHom and whose object map is
identity. Neither the strict-fibre unit map nor the diagonal unit is assumed weak.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialCategoryWholeBarFibreDegree
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeBarFibreLocalization
open DaggerOriginalSimplicialCategoryWholeHomTransport
open DaggerOriginalSimplicialCategoryWholeBarFibreTransport
open DaggerOriginalSimplicialCategoryWholeTransportNaturality
universe u
namespace DaggerOriginalSimplicialCategoryWholeFibreTransportNaturality
noncomputable section

/-- Actual whole strict-fibre transport is natural for every original enriched functor. -/
theorem wholeBarFibreTransport_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    {x y : C.Obj} (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    wholeBarFibreMap F y ≫ wholeBarFibreTransport D ((F.map x y).app (op ⦋0⦌) a) =
      wholeBarFibreTransport C a ≫ wholeBarFibreMap F x := by
  apply (cancel_epi (wholeBarHomFibreIso C y).hom).mp
  calc
    (wholeBarHomFibreIso C y).hom ≫
        (wholeBarFibreMap F y ≫ wholeBarFibreTransport D ((F.map x y).app (op ⦋0⦌) a)) =
      (originalHomSumMap F y ≫ (wholeBarHomFibreIso D (F.obj y)).hom) ≫
        wholeBarFibreTransport D ((F.map x y).app (op ⦋0⦌) a) := by
          rw [← Category.assoc, ← wholeBarHomFibreIso_natural]
    _ = originalHomSumMap F y ≫
        (wholeHomPrecompose D ((F.map x y).app (op ⦋0⦌) a) ≫
          (wholeBarHomFibreIso D (F.obj x)).hom) := by
      rw [Category.assoc, wholeBarFibreTransport_hom]
    _ = (wholeHomPrecompose C a ≫ originalHomSumMap F x) ≫
        (wholeBarHomFibreIso D (F.obj x)).hom := by
      rw [← Category.assoc, wholeHomPrecompose_natural]
    _ = wholeHomPrecompose C a ≫
        ((wholeBarHomFibreIso C x).hom ≫ wholeBarFibreMap F x) := by
      rw [Category.assoc, wholeBarHomFibreIso_natural]
    _ = (wholeBarHomFibreIso C y).hom ≫
        (wholeBarFibreTransport C a ≫ wholeBarFibreMap F x) := by
      rw [← Category.assoc, ← Category.assoc, wholeBarFibreTransport_hom]

/-- The actual entire original Hom localization commutes with the actual whole transport. -/
theorem wholeHomLocalization_transport (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    wholeHomLocalization C y ≫
        wholeHomPrecompose (completion C) ((localizationHom C x y).app (op ⦋0⦌) a) =
      wholeHomPrecompose C a ≫ wholeHomLocalization C x := by
  rw [← originalHomSumMap_localization, ← originalHomSumMap_localization]
  exact wholeHomPrecompose_natural (localization C) a

/-- The actual localization restricted to whole strict fibres commutes with original transport. -/
theorem wholeBarFibreLocalization_transport (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    wholeBarFibreMap (localization C) y ≫
        wholeBarFibreTransport (completion C) ((localizationHom C x y).app (op ⦋0⦌) a) =
      wholeBarFibreTransport C a ≫ wholeBarFibreMap (localization C) x :=
  wholeBarFibreTransport_natural (localization C) a

end
end DaggerOriginalSimplicialCategoryWholeFibreTransportNaturality
