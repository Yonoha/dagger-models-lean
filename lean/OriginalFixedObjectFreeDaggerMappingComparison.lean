import OriginalFixedObjectCotensorInverseDagger
import OriginalFixedObjectFreeDaggerGroupoidQuillen
import OriginalSimplicialEquivariantEnrichedAdjunction
import OriginalFixedObjectNativeMappingComparison

/-!
# Full mapping comparison for the actual free dagger groupoid

Transpose the unchanged equivariant Hom evaluation through every original strict
cotensor. The actual ordinary free adjunction supplies an isomorphism in every
dimension, and parameter naturality supplies all face and degeneracy maps. The
result compares full native mapping simplicial sets with the original equivariant
mapping object, without asserting a derived mapping-space identification.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectOrdinaryCellAdjunction
open DaggerOriginalFixedObjectFreeDaggerGroupoidQuillen
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectCotensorInverseDagger DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalSimplicialEquivariantParameterTensor
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
universe u
namespace DaggerOriginalFixedObjectFreeDaggerMappingComparison
noncomputable section

/-- Evaluation retains the internal-Hom image of each original inverse-dagger action. -/
theorem evaluation_cotensor_action (K : SSet.{u}) (C : FixedStrictDaggerGroupoids TwoObjects)
    (g : C2.{u}) :
    (((daggerEvaluation.obj (strictDaggerCotensor K C)).ρ g).asHom) =
      (ihom K).map (((daggerEvaluation.obj C).ρ g).asHom) := by
  rcases originalC2_cases g with rfl | rfl
  · rw [(daggerEvaluation.obj (strictDaggerCotensor K C)).ρ.map_one,
      (daggerEvaluation.obj C).ρ.map_one]
    change 𝟙 _ = (ihom K).map (𝟙 _)
    rw [CategoryTheory.Functor.map_id]
  · rw [daggerEvaluation_generator, daggerEvaluation_generator,
      strictDaggerCotensor_sigmaHom]

/-- Uncurry the entire original equivariant Hom map, with action on the first factor. -/
def uncurryAction (K : SSet.{u}) (A : Action SSet.{u} C2.{u})
    (C : FixedStrictDaggerGroupoids TwoObjects)
    (f : A ⟶ daggerEvaluation.obj (strictDaggerCotensor K C)) :
    simplicialParameterTensor A K ⟶ daggerEvaluation.obj C where
  hom := (β_ A.V K).hom ≫ uncurry f.hom
  comm g := by
    apply NatTrans.ext
    funext n p
    rcases p with ⟨e, k⟩
    have h := congrFun (NatTrans.congr_app (f.comm g) n) e
    change f.hom.app n (((A.ρ g).asHom).app n e) =
      (((daggerEvaluation.obj (strictDaggerCotensor K C)).ρ g).asHom).app n
        (f.hom.app n e) at h
    rw [evaluation_cotensor_action] at h
    exact congrArg (fun z ↦ z.app n (𝟙 n) k) h

/-- Curry each full parameter family, retaining equivariance of every original action element. -/
def curryAction (K : SSet.{u}) (A : Action SSet.{u} C2.{u})
    (C : FixedStrictDaggerGroupoids TwoObjects)
    (q : simplicialParameterTensor A K ⟶ daggerEvaluation.obj C) :
    A ⟶ daggerEvaluation.obj (strictDaggerCotensor K C) where
  hom := curry ((β_ K A.V).hom ≫ q.hom)
  comm g := by
    apply NatTrans.ext
    funext n e
    change (curry ((β_ K A.V).hom ≫ q.hom)).app n (((A.ρ g).asHom).app n e) =
      (((daggerEvaluation.obj (strictDaggerCotensor K C)).ρ g).asHom).app n
        ((curry ((β_ K A.V).hom ≫ q.hom)).app n e)
    rw [evaluation_cotensor_action]
    apply Functor.HomObj.ext
    funext m i k
    have ha := (congrFun (((A.ρ g).asHom).naturality i) e).symm
    change A.V.map i (((A.ρ g).asHom).app n e) =
      ((A.ρ g).asHom).app m (A.V.map i e) at ha
    change q.hom.app m (A.V.map i (((A.ρ g).asHom).app n e), k) =
      ((daggerEvaluation.obj C).ρ g).asHom.app m (q.hom.app m (A.V.map i e, k))
    rw [ha]
    exact congrFun (NatTrans.congr_app (q.comm g) m) (A.V.map i e, k)

/-- Exact equivariant currying on all original simplicial parameters. -/
def cotensorActionHomEquiv (K : SSet.{u}) (A : Action SSet.{u} C2.{u})
    (C : FixedStrictDaggerGroupoids TwoObjects) :
    (A ⟶ daggerEvaluation.obj (strictDaggerCotensor K C)) ≃
      (simplicialParameterTensor A K ⟶ daggerEvaluation.obj C) where
  toFun := uncurryAction K A C
  invFun := curryAction K A C
  left_inv f := by
    apply Action.Hom.ext
    change curry ((β_ K A.V).hom ≫ ((β_ A.V K).hom ≫ uncurry f.hom)) = f.hom
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  right_inv q := by
    apply Action.Hom.ext
    change (β_ A.V K).hom ≫ uncurry (curry ((β_ K A.V).hom ≫ q.hom)) = q.hom
    rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- Parameter restriction is precisely precomposition on the original product's second factor. -/
theorem uncurryAction_parameter {K L : SSet.{u}} (i : K ⟶ L)
    (A : Action SSet.{u} C2.{u}) (C : FixedStrictDaggerGroupoids TwoObjects)
    (f : A ⟶ daggerEvaluation.obj (strictDaggerCotensor L C)) :
    uncurryAction K A C
      (f ≫ daggerEvaluation.map (ObjectProperty.homMk (daggerCotensorPre i C.obj))) =
        simplicialParameterTensorMap A i ≫ uncurryAction L A C f := by
  apply Action.Hom.ext
  apply NatTrans.ext
  funext n p
  rfl

/-- The actual free dagger adjunction at each original strict cotensor. -/
def parameterHomEquiv (K : SSet.{u}) (A : Action SSet.{u} C2.{u})
    (C : FixedStrictDaggerGroupoids TwoObjects) :
    (freeDaggerGroupoid.obj A ⟶ strictDaggerCotensor K C) ≃
      (simplicialParameterTensor A K ⟶ daggerEvaluation.obj C) :=
  (freeDaggerGroupoidAdjunction.homEquiv A (strictDaggerCotensor K C)).trans
    (cotensorActionHomEquiv K A C)

/-- All simplex restrictions commute with the same original full adjunction. -/
theorem parameterHomEquiv_natural {K L : SSet.{u}} (i : K ⟶ L)
    (A : Action SSet.{u} C2.{u}) (C : FixedStrictDaggerGroupoids TwoObjects)
    (f : freeDaggerGroupoid.obj A ⟶ strictDaggerCotensor L C) :
    parameterHomEquiv K A C (f ≫ ObjectProperty.homMk (daggerCotensorPre i C.obj)) =
      simplicialParameterTensorMap A i ≫ parameterHomEquiv L A C f := by
  change uncurryAction K A C
    (freeDaggerGroupoidAdjunction.homEquiv A _ (f ≫ _)) = _
  rw [freeDaggerGroupoidAdjunction.homEquiv_naturality_right]
  exact uncurryAction_parameter i A C _

/-- The original cotensor mapping presentation is isomorphic to the full equivariant mapping. -/
def cotensorMappingIso (A : Action SSet.{u} C2.{u})
    (C : FixedStrictDaggerGroupoids TwoObjects) :
    DaggerOriginalFixedObjectCompletionMappingComparison.strictDaggerMapping
      (freeDaggerGroupoid.obj A) C ≅ enrichedMapping A (daggerEvaluation.obj C) := by
  refine NatIso.ofComponents
    (fun n ↦ (parameterHomEquiv (SSet.stdSimplex.obj n.unop) A C).toIso) ?_
  intro n m i
  funext f
  exact parameterHomEquiv_natural (SSet.stdSimplex.map i.unop) A C f

/-- Full native mapping objects of the actual free dagger groupoid satisfy the comparison. -/
def freeDaggerMappingIso (A : Action SSet.{u} C2.{u})
    (C : FixedStrictDaggerGroupoids TwoObjects) :
    (freeDaggerGroupoid.obj A ⟶[SSet.{u}] C) ≅ enrichedMapping A (daggerEvaluation.obj C) :=
  DaggerOriginalFixedObjectNativeMappingComparison.daggerMappingIso _ _ ≪≫
    (DaggerOriginalFixedObjectNativeMappingComparison.strictDaggerMappingIso _ _).symm ≪≫
      cotensorMappingIso A C

end
end DaggerOriginalFixedObjectFreeDaggerMappingComparison
