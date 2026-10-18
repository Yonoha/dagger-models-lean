import NativeCotensorParameterDiagonal
import NativeThickeningContractionEndpoints
import NativeIhomPreApply

/-! Whole original functor naturality and constant-time evaluation of parameter diagonals. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DaggerModels DaggerOriginalCotensorPrecompositionWeak
open DaggerNativeOriginalCotensorFunctor DaggerNativeCotensorParameterDiagonal
open DaggerNativeIhomParameterDiagonal DaggerNativeThickeningContractionEndpoints
open DaggerOriginalFixedObjectCotensorPoints
open DaggerNativeIhomPreApply
universe u
namespace DaggerNativeCotensorParameterDiagonalNaturality
noncomputable section

/-- Arbitrary original enriched functors commute with evaluation along a parameter graph. -/
theorem functor_naturality {I K : SSet.{u}} (theta : K ⟶ I)
    {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    map I (map K F) ≫ evaluationAlong theta D = evaluationAlong theta C ≫ map K F := by
  apply EnrichedFunctor.ext SSet
    (F := map I (map K F) ≫ evaluationAlong theta D)
    (G := evaluationAlong theta C ≫ map K F) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact diagonalHom_naturality theta (F.map x y)

/-- Pulling back the original parameter commutes with the entire graph-evaluation functor. -/
theorem parameter_naturality {I K L : SSet.{u}} (theta : K ⟶ I) (f : L ⟶ K)
    (C : SimplicialCat.{u, u}) :
    map I (DaggerNativeCoherentCotensorConstants.restrictionFunctor f C) ≫
        evaluationAlong (f ≫ theta) C =
      evaluationAlong theta C ≫ DaggerNativeCoherentCotensorConstants.restrictionFunctor f C := by
  apply EnrichedFunctor.ext SSet
    (F := map I (DaggerNativeCoherentCotensorConstants.restrictionFunctor f C) ≫
      evaluationAlong (f ≫ theta) C)
    (G := evaluationAlong theta C ≫
      DaggerNativeCoherentCotensorConstants.restrictionFunctor f C) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext q F
  apply Functor.HomObj.ext
  funext r a k
  change ((((MonoidalClosed.pre f).app (C.enriched.Hom x y)).app r
    (F.app r a (theta.app r (f.app r k)))).app r (𝟙 r) k) =
      ((((MonoidalClosed.pre f).app (C.enriched.Hom x y)).app q
        ((diagonalHom theta (C.enriched.Hom x y)).app q F)).app r a k)
  rw [pre_app_apply, pre_app_apply]
  rfl

/-- A constant graph is exactly the existing native evaluation in the outer parameter. -/
theorem constant_parameter {I K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ I)
    (C : SimplicialCat.{u, u}) :
    evaluationAlong (toUnit K ≫ a) C = evaluationFunctor a (originalCotensor K C) := by
  apply EnrichedFunctor.ext SSet
    (F := evaluationAlong (toUnit K ≫ a) C)
    (G := evaluationFunctor a (originalCotensor K C)) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext q F
  apply Functor.HomObj.ext
  funext r b k
  have ha := congrFun (a.naturality b) PUnit.unit
  have hF := congrFun (F.naturality b (𝟙 q)) (a.app q PUnit.unit)
  change F.app r ((𝟙 q) ≫ b) (I.map b (a.app q PUnit.unit)) =
    ((ihom K).obj (C.enriched.Hom x y)).map b
      (F.app q (𝟙 q) (a.app q PUnit.unit)) at hF
  rw [Category.id_comp] at hF
  change (F.app r b (a.app r PUnit.unit)).app r (𝟙 r) k =
    (F.app q (𝟙 q) (a.app q PUnit.unit)).app r b k
  change a.app r PUnit.unit = I.map b (a.app q PUnit.unit) at ha
  rw [ha]
  have h := congrArg (fun g ↦ g.app r (𝟙 r) k) hF
  change (F.app r b (I.map b (a.app q PUnit.unit))).app r (𝟙 r) k =
    (F.app q (𝟙 q) (a.app q PUnit.unit)).app r (b ≫ 𝟙 r) k at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- Native outer evaluation commutes with all original object-changing enriched functors. -/
theorem evaluation_naturality {I : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ I)
    {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    map I F ≫ evaluationFunctor a D = evaluationFunctor a C ≫ F := by
  apply EnrichedFunctor.ext SSet (F := map I F ≫ evaluationFunctor a D)
    (G := evaluationFunctor a C ≫ F) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact pointEvaluation_natural a (F.map x y)

end
end DaggerNativeCotensorParameterDiagonalNaturality
