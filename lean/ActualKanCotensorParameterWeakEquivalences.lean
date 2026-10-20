import OriginalSimplicialCotensorRestriction
import OriginalContravariantCofibrantBrownChallengeProof
import ActualQSingularFibrantWeakEquivalences

/-! Restriction of a weakly equivalent parameter is weak into an actual Kan complex. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed HomotopicalAlgebra Opposite
open DaggerOriginalSimplicialCotensorRestriction DaggerOriginalFixedObjectCotensorPoints
open DaggerOrdinaryAnodyneTensor DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualKanCotensorParameterWeakEquivalences
noncomputable section

/-- The contravariant functor uses the native internal Hom and its original restriction. -/
def parameterFunctor (X : SSet.{u}) : SSet.{u}ᵒᵖ ⥤ SSet.{u} where
  obj K := (ihom K.unop).obj X
  map i := (MonoidalClosed.pre i.unop).app X
  map_id K := by
    simpa only [NatTrans.id_app] using
      congrArg (fun t ↦ t.app X) (MonoidalClosed.pre_id K.unop)
  map_comp i j := by
    simpa only [unop_comp, NatTrans.comp_app] using
      congrArg (fun t ↦ t.app X) (MonoidalClosed.pre_map j.unop i.unop)

/-- The native anodyne characterization and existing cotensor theorem supply Brown's premise. -/
theorem pre_trivialCofibration_weakEquivalence {A B : SSet.{u}} (i : A ⟶ B)
    [Cofibration i] [WeakEquivalence i] (X : SSet.{u}) [X.KanComplex] :
    WeakEquivalence ((MonoidalClosed.pre i).app X) := by
  have ha : SSet.anodyneExtensions i :=
    (anodyne_iff_trivialCofibration i).2 (mem_trivialCofibrations i)
  exact ((mem_trivialFibrations_iff _).1 (pre_trivialFibration i ha X)).2

/-- All simplicial sets are cofibrant, so the existing contravariant Brown theorem applies. -/
theorem pre_weakEquivalence {A B : SSet.{u}} (i : A ⟶ B) [WeakEquivalence i]
    (X : SSet.{u}) [X.KanComplex] : WeakEquivalence ((MonoidalClosed.pre i).app X) := by
  exact DaggerOriginalContravariantCofibrantBrownChallengeProof.challengeProof
    SSet SSet (parameterFunctor X) (by
      intro K L j hj hw
      have : Cofibration j := hj
      have : WeakEquivalence j := hw
      exact pre_trivialCofibration_weakEquivalence j X)
    inferInstance inferInstance i inferInstance

/-- Restriction is geometrically weak with exactly the original parameter arrow. -/
theorem pre_GW {A B : SSet.{u}} (i : A ⟶ B) (hi : GW i)
    (X : SSet.{u}) [X.KanComplex] : GW ((MonoidalClosed.pre i).app X) := by
  have : WeakEquivalence i := (weakEquivalence_iff_GW i).2 hi
  exact (weakEquivalence_iff_GW _).1 (pre_weakEquivalence i X)

/-- Native constants commute with every actual restriction of the simplicial parameter. -/
theorem constantHom_parameter {K L : SSet.{u}} (i : K ⟶ L) (X : SSet.{u}) :
    constantHom L X ≫ (MonoidalClosed.pre i).app X = constantHom K X := by
  unfold constantHom
  rw [MonoidalClosed.curry_pre_app]
  congr 1

/-- The constants for K are the original unit constants followed by terminal restriction. -/
theorem constantHom_factor (K X : SSet.{u}) :
    constantHom (𝟙_ SSet.{u}) X ≫ (MonoidalClosed.pre (toUnit K)).app X =
      constantHom K X :=
  constantHom_parameter (toUnit K) X

/-- Weak contractibility of the parameter makes the literal constant map weak. -/
theorem constantHom_GW (K X : SSet.{u}) [X.KanComplex] (hK : GW (toUnit K)) :
    GW (constantHom K X) := by
  have : IsIso (constantHom (𝟙_ SSet.{u}) X) :=
    ⟨⟨pointEvaluation (𝟙 (𝟙_ SSet.{u})) X,
      constantHom_evaluation (𝟙 (𝟙_ SSet.{u})) X, unitEvaluation_constantHom X⟩⟩
  have : WeakEquivalence ((MonoidalClosed.pre (toUnit K)).app X) :=
    (weakEquivalence_iff_GW _).2 (pre_GW (toUnit K) hK X)
  apply (weakEquivalence_iff_GW _).1
  rw [← constantHom_factor]
  infer_instance

end
end DaggerActualKanCotensorParameterWeakEquivalences
