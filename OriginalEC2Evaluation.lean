import OriginalUnitaryCoreCanonicalVertices
import TopCatModelCategory.SSet.SingularConnected

/-!
# Evaluation on the actual original equivariant mapping space

Evaluation at any point of the original realized codiscrete nerve is
continuous and natural in the target action. Singular evaluation sends the
original canonical constant vertex to the original realization-singular
unit vertex. The distinguished point is the realization of the identity
object in the literal original codiscrete group.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalDaggerRealizationVertices
open DaggerOriginalDaggerRealizationContinuousAction DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2RealizationAction DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalEC2HomotopyFixedPointFunctor

universe u

namespace DaggerOriginalEC2Evaluation

noncomputable section

/-- The specified original identity vertex of the codiscrete group, realized. -/
def identityPoint : realizedEC2ContinuousAction.{u}.obj.V :=
  SSet.toTopObjMk (ComposableArrows.mk₀ (Codiscrete.mk (1 : C2.{u})))

/-- Actual continuous evaluation on the original compact-open equivariance subtype. -/
def evaluationTop (X : ContAction TopCat.{u} C2.{u})
    (e : realizedEC2ContinuousAction.{u}.obj.V) : mappingTop X ⟶ X.obj.V :=
  TopCat.ofHom ⟨fun q ↦ q.val e, (continuous_eval_const e).comp continuous_subtype_val⟩

/-- Postcomposition and evaluation commute on the original topological maps. -/
theorem evaluationTop_naturality {X Y : ContAction TopCat.{u} C2.{u}} (f : X ⟶ Y)
    (e : realizedEC2ContinuousAction.{u}.obj.V) :
    postcompose f ≫ evaluationTop Y e = evaluationTop X e ≫ f.hom.hom := by
  ext q
  rfl

/-- Singular evaluation of the original realized dagger mapping construction. -/
def daggerEvaluation (K : DaggerSSet.{u}) (e : realizedEC2ContinuousAction.{u}.obj.V) :
    daggerHomotopyFixedPointFunctor.obj K ⟶ TopCat.toSSet.obj (SSet.toTop.obj K.toSSet) :=
  TopCat.toSSet.map (evaluationTop (realizedContinuousActionFunctor.obj K) e)

/-- Singular evaluation is natural for the original dagger morphisms. -/
theorem daggerEvaluation_naturality {K L : DaggerSSet.{u}} (f : K ⟶ L)
    (e : realizedEC2ContinuousAction.{u}.obj.V) :
    daggerHomotopyFixedPointFunctor.map f ≫ daggerEvaluation L e =
      daggerEvaluation K e ≫ TopCat.toSSet.map (SSet.toTop.map f.hom) := by
  change TopCat.toSSet.map (postcompose (realizedContinuousActionFunctor.map f)) ≫
    TopCat.toSSet.map (evaluationTop (realizedContinuousActionFunctor.obj L) e) = _
  rw [← Functor.map_comp, evaluationTop_naturality, Functor.map_comp]
  rfl

/-- The constant singular vertex at the literal original realized vertex. -/
def realizedSingularVertex (K : DaggerSSet.{u}) (x : K.toSSet.obj (op ⦋0⦌)) :
    (TopCat.toSSet.obj (SSet.toTop.obj K.toSSet)).obj (op ⦋0⦌) :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ (realizedVertex K x))

/-- Evaluating the original constant homotopy-fixed vertex retains its exact realized label. -/
theorem daggerEvaluation_canonical (K : DaggerSSet.{u})
    (x : K.toSSet.obj (op ⦋0⦌)) (e : realizedEC2ContinuousAction.{u}.obj.V) :
    (daggerEvaluation K e).app (op ⦋0⦌) (canonicalZeroSimplex K x) =
      realizedSingularVertex K x := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext t
  rfl

/-- The realized constant vertex is exactly the original realization-singular unit vertex. -/
theorem realizedSingularVertex_eq_unit (K : DaggerSSet.{u})
    (x : K.toSSet.obj (op ⦋0⦌)) :
    realizedSingularVertex K x = (sSetTopAdj.unit.app K.toSSet).app (op ⦋0⦌) x := by
  let z : (Δ[0] : SSet.{u}).obj (op ⦋0⦌) := SSet.stdSimplex.obj₀Equiv.symm 0
  have hv : (vertexMap K x).app (op ⦋0⦌) z = x := by
    have hz : z = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply SSet.stdSimplex.obj₀Equiv.injective
      apply Fin.ext
      omega
    rw [hz, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact SSet.yonedaEquiv.apply_symm_apply x
  have hn := congrFun (NatTrans.congr_app
    (sSetTopAdj.unit.naturality (vertexMap K x)) (op ⦋0⦌)) z
  change (sSetTopAdj.unit.app K.toSSet).app (op ⦋0⦌)
    ((vertexMap K x).app (op ⦋0⦌) z) =
    (TopCat.toSSet.map (SSet.toTop.map (vertexMap K x))).app (op ⦋0⦌)
      ((sSetTopAdj.unit.app (Δ[0] : SSet.{u})).app (op ⦋0⦌) z) at hn
  rw [hv] at hn
  rw [hn]
  apply TopCat.toSSetObj₀Equiv.injective
  change (SSet.toTop.map (vertexMap K x)) _ = (SSet.toTop.map (vertexMap K x)) _
  congr 1
  exact Subsingleton.elim _ _

end

end DaggerOriginalEC2Evaluation
