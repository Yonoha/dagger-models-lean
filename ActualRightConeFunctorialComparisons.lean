import ActualRightConeSingularComparisonIso
import ActualQKanNaturalComparisons
import ActualQRealizationQuillen

/-! Literal right-cone postcomposition retains every enriched Hom map and both vertices. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightCone DaggerOriginalEnrichedHomTransport
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerChosenRigidificationNecklace hiding C RV
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRightConeFunctorialComparisons
noncomputable section

variable {D E : SimplicialCat.{u, u}} (F : D ⟶ E)
variable (v w : (coherentNerve.obj D).obj (op ⦋0⦌))

/-- The literal target vertex under the original coherent nerve. -/
def vertexMap (v : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    (coherentNerve.obj E).obj (op ⦋0⦌) := (coherentNerve.map F).app (op ⦋0⦌) v

/-- Postcompose each actual cone simplex with the original coherent-nerve map. -/
def postcomp : rightConeSimplices D v w ⟶
    rightConeSimplices E (vertexMap F v) (vertexMap F w) where
  app q σ := ⟨σ.1 ≫ coherentNerve.map F, by
    constructor
    · change (coherentNerve.map F).app (op ⦋0⦌) (σ.1.app _ (alpha q.unop.len)) = _
      rw [σ.2.1]
      rfl
    · change (coherentNerve.map F).app (op ⦋0⦌) (σ.1.app _ (omega q.unop.len)) = _
      rw [σ.2.2]
      rfl⟩
  naturality q r f := by
    funext σ
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- Evaluation at the two native vertices is definitionally the original enriched Hom map. -/
def homMap : (NerveVertices.vertexEquiv D v ⟶[SSet.{u}] NerveVertices.vertexEquiv D w) ⟶
    (NerveVertices.vertexEquiv E (vertexMap F v) ⟶[SSet.{u}]
      NerveVertices.vertexEquiv E (vertexMap F w)) :=
  F.map (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w)

/-- Both endpoint equations for the actual evaluated cone functor. -/
theorem evaluation_objects (n : ℕ) (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    (rigidification.map σ.1 ≫ rigidificationCoherentNerveAdjunction.counit.app D).obj
        (alphaObj n) = NerveVertices.vertexEquiv D v ∧
    (rigidification.map σ.1 ≫ rigidificationCoherentNerveAdjunction.counit.app D).obj
        (omegaObj n) = NerveVertices.vertexEquiv D w :=
  ⟨(evaluation_alpha_obj D n σ.1).trans (congrArg (NerveVertices.vertexEquiv D) σ.2.1),
    (evaluation_omega_obj D n σ.1).trans (congrArg (NerveVertices.vertexEquiv D) σ.2.2)⟩

/-- The fixed-endpoint evaluation uses the Hom of precisely the original evaluated functor. -/
theorem evaluation_as_transport (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    rightConeEvaluation D v w n σ =
      (rigidification.map σ.1 ≫ rigidificationCoherentNerveAdjunction.counit.app D).map
        (alphaObj n) (omegaObj n) ≫
      targetHomTransport (evaluation_objects v w n σ).1 (evaluation_objects v w n σ).2 := by
  simp only [rightConeEvaluation, DaggerOriginalCounitRightCone.evaluation,
    SimplicialCat.comp_map, Category.assoc, targetHomTransport, eqToHom_trans]

/-- Naturality retains the literal counit, all cone simplices and both endpoint transports. -/
theorem evaluation_postcomp (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    rightConeEvaluation E (vertexMap F v) (vertexMap F w) n ((postcomp F v w).app _ σ) =
      rightConeEvaluation D v w n σ ≫ homMap F v w := by
  let τ := (postcomp F v w).app (op ⦋n⦌) σ
  have hfunctor :
      rigidification.map τ.1 ≫ rigidificationCoherentNerveAdjunction.counit.app E =
        (rigidification.map σ.1 ≫ rigidificationCoherentNerveAdjunction.counit.app D) ≫ F := by
    change rigidification.map (σ.1 ≫ coherentNerve.map F) ≫
      rigidificationCoherentNerveAdjunction.counit.app E = _
    have hn : rigidification.map (coherentNerve.map F) ≫
        rigidificationCoherentNerveAdjunction.counit.app E =
      rigidificationCoherentNerveAdjunction.counit.app D ≫ F :=
      rigidificationCoherentNerveAdjunction.counit.naturality F
    rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc]
  rw [evaluation_as_transport, evaluation_as_transport]
  have h := enrichedFunctor_hom_congr_to_fixed hfunctor (alphaObj n) (omegaObj n)
    (NerveVertices.vertexEquiv E (vertexMap F v))
    (NerveVertices.vertexEquiv E (vertexMap F w))
    (evaluation_objects (vertexMap F v) (vertexMap F w) n τ).1
    (evaluation_objects (vertexMap F v) (vertexMap F w) n τ).2
    (congrArg F.obj (evaluation_objects v w n σ).1)
    (congrArg F.obj (evaluation_objects v w n σ).2)
  refine h.trans ?_
  change (_ ≫ F.map _ _) ≫ targetHomTransport _ _ =
    (_ ≫ targetHomTransport _ _) ≫ F.map _ _
  rw [Category.assoc, Category.assoc, enriched_map_endpoint_transport]

/-- The actual cone-to-singular isomorphism is natural for every enriched functor. -/
theorem comparison_naturality :
    postcomp F v w ≫ coneSingularComparison E (vertexMap F v) (vertexMap F w) =
      coneSingularComparison D v w ≫
        DaggerOriginalCounitRightConeQRealizationAdjunction.singular.map (homMap F v w) := by
  ext q σ
  apply ULift.ext
  change ((coneSingularComparison E (vertexMap F v) (vertexMap F w)).app q
      ((postcomp F v w).app q σ)).down =
    ((coneSingularComparison D v w).app q σ).down ≫ homMap F v w
  rw [coneSingularComparison_app, coneSingularComparison_app]
  exact evaluation_postcomp F v w q.unop.len σ

/-- The actual right-cone map creates the original Hom weak class between locally Kan targets. -/
theorem postcomp_GW_iff
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y))
    (hE : ∀ x y : E.Obj, SSet.KanComplex (E.enriched.Hom x y)) :
    DaggerSSetGluing.GW (postcomp F v w) ↔ DaggerSSetGluing.GW (homMap F v w) := by
  have := hD (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w)
  have := hE (NerveVertices.vertexEquiv E (vertexMap F v))
    (NerveVertices.vertexEquiv E (vertexMap F w))
  have : IsIso (coneSingularComparison D v w) :=
    DaggerActualRightConeSingularComparisonIso.comparison_isIso D v w
  have : IsIso (coneSingularComparison E (vertexMap F v) (vertexMap F w)) :=
    DaggerActualRightConeSingularComparisonIso.comparison_isIso _ _ _
  have : WeakEquivalence (coneSingularComparison D v w) := inferInstance
  have : WeakEquivalence (coneSingularComparison E (vertexMap F v) (vertexMap F w)) :=
    inferInstance
  rw [← DaggerActualQKanNaturalComparisons.singular_GW_iff (homMap F v w),
    ← DaggerSSetGluing.weakEquivalence_iff_GW,
    ← DaggerSSetGluing.weakEquivalence_iff_GW]
  calc
    WeakEquivalence (postcomp F v w) ↔
        WeakEquivalence (postcomp F v w ≫
          coneSingularComparison E (vertexMap F v) (vertexMap F w)) :=
      (weakEquivalence_postcomp_iff _ _).symm
    _ ↔ WeakEquivalence (coneSingularComparison D v w ≫
        DaggerOriginalCounitRightConeQRealizationAdjunction.singular.map (homMap F v w)) := by
      rw [comparison_naturality]
    _ ↔ WeakEquivalence
        (DaggerOriginalCounitRightConeQRealizationAdjunction.singular.map (homMap F v w)) :=
      weakEquivalence_precomp_iff _ _

end
end DaggerActualRightConeFunctorialComparisons
