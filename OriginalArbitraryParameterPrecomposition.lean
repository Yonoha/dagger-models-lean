import OriginalSimplicialCategorySimplexTransportWeakEquivalence
import NativeProductProjectionBaseChange

/-! Relative original precomposition is weak for any parameter when the two target Homs are Kan. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open HomotopicalAlgebra DaggerModels
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalSimplicialCategorySimplexTransport
open DaggerOriginalSimplicialCategorySimplexTransportWeakEquivalence
open DaggerNativeProductProjectionBaseChange DaggerNativeFibrewiseWeakRecognition
open DaggerNativeSimplexPullbackFibrationDetection
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalArbitraryParameterPrecomposition
noncomputable section

def parameterPrecompose (C : SimplicialCat.{u, u}) {x y : C.Obj} {K : SSet.{u}}
    (a : K ⟶ C.enriched.Hom x y) (z : C.Obj) :
    K ⊗ C.enriched.Hom y z ⟶ C.enriched.Hom x z :=
  (a ⊗ₘ 𝟙 _) ≫ C.enriched.comp x y z

def relativeParameterPrecompose (C : SimplicialCat.{u, u}) {x y : C.Obj} {K : SSet.{u}}
    (a : K ⟶ C.enriched.Hom x y) (z : C.Obj) :
    K ⊗ C.enriched.Hom y z ⟶ K ⊗ C.enriched.Hom x z :=
  lift (fst _ _) (parameterPrecompose C a z)

theorem relativeParameterPrecompose_fst (C : SimplicialCat.{u, u})
    {x y : C.Obj} {K : SSet.{u}} (a : K ⟶ C.enriched.Hom x y) (z : C.Obj) :
    relativeParameterPrecompose C a z ≫ fst _ _ = fst _ _ := by
  apply NatTrans.ext
  rfl

theorem relativeParameterPrecompose_baseChange (C : SimplicialCat.{u, u})
    {x y : C.Obj} {K V : SSet.{u}} (a : K ⟶ C.enriched.Hom x y) (z : C.Obj) (b : V ⟶ K) :
    (b ⊗ₘ 𝟙 (C.enriched.Hom y z)) ≫ relativeParameterPrecompose C a z =
      relativeParameterPrecompose C (b ≫ a) z ≫ (b ⊗ₘ 𝟙 (C.enriched.Hom x z)) := by
  apply NatTrans.ext
  rfl

theorem relativeParameterPrecompose_weak (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) {x y : C.Obj} {K : SSet.{u}}
    (a : K ⟶ C.enriched.Hom x y) (z : C.Obj)
    [hX : (C.enriched.Hom y z).KanComplex] [hY : (C.enriched.Hom x z).KanComplex] :
    WeakEquivalence (relativeParameterPrecompose C a z) := by
  have : Fibration (fst K (C.enriched.Hom y z)) := product_projection_fibration _ _
  have : Fibration (fst K (C.enriched.Hom x z)) := product_projection_fibration _ _
  apply weak_of_vertex_base_changes (fst K (C.enriched.Hom y z))
    (fst K (C.enriched.Hom x z)) (relativeParameterPrecompose C a z)
    (relativeParameterPrecompose_fst C a z)
  intro b
  let σ := SSet.yonedaEquiv (b ≫ a)
  have hb : b ≫ a = SSet.yonedaEquiv.symm σ := by simp [σ]
  have hf := productBaseChangeIso_map b (relativeParameterPrecompose C a z)
    (relativeParameterPrecompose_fst C a z) (relativeSimplexPrecompose C σ z)
    (relativeSimplexPrecompose_fst C σ z) (by
      rw [relativeParameterPrecompose_baseChange, hb]
      rfl)
  have : WeakEquivalence (relativeSimplexPrecompose C σ z) :=
    relativeSimplexPrecompose_weakEquivalence_of_actualGroupoid C hC σ z
  have : WeakEquivalence ((productBaseChangeIso b (C.enriched.Hom y z)).hom) :=
    inferInstance
  have : WeakEquivalence (relativeSimplexPrecompose C σ z ≫
      (productBaseChangeIso b (C.enriched.Hom x z)).hom) := inferInstance
  exact weakEquivalence_of_precomp_of_fac hf

end
end DaggerOriginalArbitraryParameterPrecomposition
