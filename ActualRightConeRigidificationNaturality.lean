import ActualRightConeKanMapping
import ActualQRealizationWeakReflection

/-! Naturality of the literal rigidification comparison and right-cone local weak recognition. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightCone DaggerOriginalEnrichedHomTransport
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeCounitFactorization
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerOriginalCounitRightConeQRealizationAdjunction hiding singular
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerActualRightConeFunctorialComparisons
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRightConeRigidificationNaturality
noncomputable section

private abbrev RV := RigidificationVertices.vertexEquiv.{u}
variable {D E : SimplicialCat.{u, u}} (F : D ⟶ E)
variable (v w : (coherentNerve.obj D).obj (op ⦋0⦌))

/-- The literal original rigidification Hom map with both original vertex transports. -/
def rigidificationHomMap :
    ((rigidification.obj (coherentNerve.obj D)).enriched.Hom
      (RV (coherentNerve.obj D) v) (RV (coherentNerve.obj D) w)) ⟶
    ((rigidification.obj (coherentNerve.obj E)).enriched.Hom
      (RV (coherentNerve.obj E) (vertexMap F v))
      (RV (coherentNerve.obj E) (vertexMap F w))) :=
  castMap (rigidification.map (coherentNerve.map F))
    (RV (coherentNerve.obj D) v) (RV (coherentNerve.obj D) w)
    (RV (coherentNerve.obj E) (vertexMap F v))
    (RV (coherentNerve.obj E) (vertexMap F w))
    (RigidificationVertices.vertexEquiv_naturality (coherentNerve.map F) v)
    (RigidificationVertices.vertexEquiv_naturality (coherentNerve.map F) w)

/-- Both endpoint equations for the original rigidified cone simplex. -/
theorem leg_objects (n : ℕ) (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    (rigidification.map σ.1).obj (alphaObj n) = RV (coherentNerve.obj D) v ∧
    (rigidification.map σ.1).obj (omegaObj n) = RV (coherentNerve.obj D) w :=
  ⟨(RigidificationVertices.vertexEquiv_naturality σ.1 (alpha n)).trans
      (congrArg (RV (coherentNerve.obj D)) σ.2.1),
    (RigidificationVertices.vertexEquiv_naturality σ.1 (omega n)).trans
      (congrArg (RV (coherentNerve.obj D)) σ.2.2)⟩

/-- The original simplex leg is the casted Hom of the original rigidification map. -/
theorem leg_as_cast (n : ℕ) (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    rightConeRigidificationLeg D v w n σ =
      castMap (rigidification.map σ.1) (alphaObj n) (omegaObj n)
        (RV (coherentNerve.obj D) v) (RV (coherentNerve.obj D) w)
        (leg_objects v w n σ).1 (leg_objects v w n σ).2 := rfl

/-- Every original cone simplex respects the exact rigidification Hom map. -/
theorem leg_postcomp (n : ℕ) (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    rightConeRigidificationLeg E (vertexMap F v) (vertexMap F w) n
        ((postcomp F v w).app _ σ) =
      rightConeRigidificationLeg D v w n σ ≫ rigidificationHomMap F v w := by
  rw [leg_as_cast, leg_as_cast]
  unfold rigidificationHomMap
  rw [← castMap_comp]
  exact castMap_congr (rigidification.map_comp σ.1 (coherentNerve.map F))
    (alphaObj n) (omegaObj n)
    (RV (coherentNerve.obj E) (vertexMap F v))
    (RV (coherentNerve.obj E) (vertexMap F w)) _ _ _ _

/-- Naturality descends through the actual Q realization, retaining the original Hom apex. -/
theorem rigidification_naturality :
    realization.map (postcomp F v w) ≫
      coneRigidificationMap E (vertexMap F v) (vertexMap F w) =
    coneRigidificationMap D v w ≫ rigidificationHomMap F v w := by
  apply (simplexCoconeIsColimit (rightConeSimplices D v w)).hom_ext
  intro σ
  let τ := CostructuredArrow.mk (σ.hom ≫ postcomp F v w)
  have hl := coneRigidificationMap_leg E (vertexMap F v) (vertexMap F w) τ
  change (realizationUnit.app σ.left ≫ realization.map σ.hom) ≫
      (realization.map (postcomp F v w) ≫
        coneRigidificationMap E (vertexMap F v) (vertexMap F w)) =
    (realizationUnit.app σ.left ≫ realization.map σ.hom) ≫
      (coneRigidificationMap D v w ≫ rigidificationHomMap F v w)
  rw [Category.assoc, ← Category.assoc (realization.map σ.hom), ← Functor.map_comp]
  change realizationUnit.app τ.left ≫ realization.map τ.hom ≫
      coneRigidificationMap E (vertexMap F v) (vertexMap F w) = _
  rw [hl, ← Category.assoc, Category.assoc (realizationUnit.app σ.left),
    coneRigidificationMap_leg]
  exact leg_postcomp F v w σ.left.len (uliftYonedaEquiv σ.hom)

/-- For locally Kan targets, right-cone maps detect weakness of every original enriched Hom. -/
theorem local_GW_iff
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y))
    (hE : ∀ x y : E.Obj, SSet.KanComplex (E.enriched.Hom x y)) :
    (∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌), GW (postcomp F v w)) ↔
      ∀ x y : D.Obj, GW (F.map x y) := by
  constructor
  · intro h x y
    obtain ⟨v, rfl⟩ := (NerveVertices.vertexEquiv D).surjective x
    obtain ⟨w, rfl⟩ := (NerveVertices.vertexEquiv D).surjective y
    exact (postcomp_GW_iff F v w hD hE).mp (h v w)
  · intro h v w
    exact (postcomp_GW_iff F v w hD hE).mpr
      (h (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w))

/-- The same original Hom test applies after the unchanged Q realization. -/
theorem realized_local_GW_iff
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y))
    (hE : ∀ x y : E.Obj, SSet.KanComplex (E.enriched.Hom x y)) :
    (∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌),
      GW (realization.map (postcomp F v w))) ↔ ∀ x y : D.Obj, GW (F.map x y) := by
  simp_rw [DaggerActualQRealizationWeakReflection.realization_GW_iff]
  exact local_GW_iff F hD hE

end
end DaggerActualRightConeRigidificationNaturality
