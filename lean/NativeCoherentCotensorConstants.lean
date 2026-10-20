import NativeGroupoidalCoherentNerveWeak
import ActualKanCotensorParameterWeakEquivalences
import OriginalCotensorPiZeroGroupoid

/-!
# Constants into the original coherent cotensor nerve

The original objects, original cotensor and original coherent nerve are retained.
Weak contractibility of the parameter and the already proved original counit give
the actual column weak equivalence needed for the coherent-diagram resolution.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open DaggerModels OrdinaryRigidification
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectCotensorPoints DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalCotensorPiZeroGroupoid
open DaggerActualKanCotensorParameterWeakEquivalences
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoherentCotensorConstants
noncomputable section

def constantFunctor (K : SSet.{u}) (C : SimplicialCat.{u, u}) :
    C ⟶ originalCotensor K C := originalHom (constant K ⟨C.enriched⟩)

def restrictionFunctor {K L : SSet.{u}} (i : K ⟶ L) (C : SimplicialCat.{u, u}) :
    originalCotensor L C ⟶ originalCotensor K C :=
  originalHom (cotensorPre i ⟨C.enriched⟩)

theorem constant_parameter {K L : SSet.{u}} (i : K ⟶ L) (C : SimplicialCat.{u, u}) :
    constantFunctor L C ≫ restrictionFunctor i C = constantFunctor K C := by
  have h : constant L ⟨C.enriched⟩ ≫ cotensorPre i ⟨C.enriched⟩ =
      constant K ⟨C.enriched⟩ := by
    apply fixedHom_ext
    intro x y
    exact constantHom_parameter i (C.enriched.Hom x y)
  exact congrArg (fun F ↦ originalHom F) h

theorem restriction_id (K : SSet.{u}) (C : SimplicialCat.{u, u}) :
    restrictionFunctor (𝟙 K) C = 𝟙 (originalCotensor K C) :=
  congrArg (fun F ↦ originalHom F) (cotensorPre_id K ⟨C.enriched⟩)

theorem restriction_comp {K L M : SSet.{u}} (i : K ⟶ L) (j : L ⟶ M)
    (C : SimplicialCat.{u, u}) :
    restrictionFunctor (i ≫ j) C = restrictionFunctor j C ≫ restrictionFunctor i C :=
  congrArg (fun F ↦ originalHom F) (cotensorPre_comp i j ⟨C.enriched⟩)

theorem cotensor_locallyKan (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (x y : (originalCotensor K C).Obj) :
    SSet.KanComplex ((originalCotensor K C).enriched.Hom x y) := by
  have := hC x y
  change SSet.KanComplex ((ihom K).obj (C.enriched.Hom x y))
  infer_instance

theorem constant_hom_weak (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hK : DaggerSSetGluing.GW (toUnit K)) (x y : C.Obj) :
    WeakEquivalence ((constantFunctor K C).map x y) := by
  have := hC x y
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2
    (constantHom_GW K (C.enriched.Hom x y) hK)

/-- The entire original coherent-nerve constant map is weak, with no vertex change. -/
theorem constant_nerve_weak (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hG : HasActualComponentGroupoid C) (hK : DaggerSSetGluing.GW (toUnit K)) :
    WeakEquivalence (coherentNerve.map (constantFunctor K C)) :=
  DaggerNativeGroupoidalCoherentNerveWeak.map_weak (constantFunctor K C) hC
    (cotensor_locallyKan K C hC) hG (cotensor_groupoid K C hG hC)
    (constant_hom_weak K C hC hK) (fun x ↦ ⟨x, rfl⟩)

end
end DaggerNativeCoherentCotensorConstants
