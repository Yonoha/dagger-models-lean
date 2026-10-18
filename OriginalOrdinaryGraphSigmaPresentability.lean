import OriginalOrdinaryGraphSigmaFunctor
import OriginalOrdinaryGraphEvaluationPreservation
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Finite accessibility of the ordinary endpoint-indexed sigma functor

The literal endpoint pullback is a finite limit of accessible Type-valued
functors. Ordinary vertex and total-edge colimit preservation comes from the
accepted original graph colimit, not from a dagger presheaf equivalence.
-/

open CategoryTheory Limits Opposite

universe u

namespace DaggerModels.OriginalOrdinaryGraphSigmaFunctor

open SimplicialGraph.TotalSpace

def pairFst : pairs.{u} ⟶ OriginalOrdinaryGraphEvaluation.vertices where
  app _ := Prod.fst

def pairSnd : pairs.{u} ⟶ OriginalOrdinaryGraphEvaluation.vertices where
  app _ := Prod.snd

def pairsCone : BinaryFan OriginalOrdinaryGraphEvaluation.vertices.{u}
    OriginalOrdinaryGraphEvaluation.vertices := BinaryFan.mk pairFst pairSnd

def pairsLift {T : SimplicialGraph.{u} ⥤ Type u}
    (f g : T ⟶ OriginalOrdinaryGraphEvaluation.vertices) : T ⟶ pairs where
  app G t := (f.app G t, g.app G t)
  naturality {G H} k := by
    funext t
    exact Prod.ext (congrFun (f.naturality k) t) (congrFun (g.naturality k) t)

def pairsIsLimit : IsLimit pairsCone.{u} := BinaryFan.IsLimit.mk _ pairsLift
  (fun _ _ ↦ by ext G t; rfl)
  (fun _ _ ↦ by ext G t; rfl)
  (fun f g m h₁ h₂ ↦ by
    ext G t
    exact Prod.ext (congrArg (fun a ↦ a.app G t) h₁)
      (congrArg (fun a ↦ a.app G t) h₂))

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A finite product of vertex evaluations preserves filtered colimits. -/
theorem pairs_isCardinalAccessible : pairs.{u}.IsCardinalAccessible Cardinal.aleph0.{u} := by
  letI := OriginalOrdinaryGraphEvaluation.vertices_preservesColimits.{u}
  letI : ∀ j, ((pair OriginalOrdinaryGraphEvaluation.vertices.{u}
      OriginalOrdinaryGraphEvaluation.vertices).obj j).IsCardinalAccessible
        Cardinal.aleph0.{u} := by
    rintro ⟨j⟩
    cases j <;> exact inferInstanceAs
      (OriginalOrdinaryGraphEvaluation.vertices.IsCardinalAccessible Cardinal.aleph0)
  exact Functor.isCardinalAccessible_of_isLimit pairsCone.{u} pairsIsLimit.{u}
    Cardinal.aleph0.{u}
    (hasCardinalLT_of_finite (Arrow (Discrete WalkingPair)) Cardinal.aleph0 le_rfl)

/-- Presentable `K` gives accessibility of the literal fixed-endpoint mapping functor. -/
theorem sigmaFunctor_isCardinalAccessible (K : SSet.{u}) [IsFinitelyPresentable.{u} K] :
    (sigmaFunctor K).IsCardinalAccessible Cardinal.aleph0.{u} := by
  letI := pairs_isCardinalAccessible.{u}
  letI := OriginalOrdinaryGraphEvaluation.edgeFunctor_preservesColimits.{u}
  letI : (edgeHoms K).IsCardinalAccessible Cardinal.aleph0.{u} :=
    inferInstanceAs ((edgeFunctor ⋙ coyoneda.obj (op K)).IsCardinalAccessible Cardinal.aleph0)
  letI : (constantHoms K).IsCardinalAccessible Cardinal.aleph0.{u} :=
    inferInstanceAs ((pairs ⋙ Functor.const SimplexCategoryᵒᵖ ⋙
      coyoneda.obj (op K)).IsCardinalAccessible Cardinal.aleph0)
  letI : (pullbackFunctor K).IsCardinalAccessible Cardinal.aleph0.{u} :=
    TypeFunctorPullback.isCardinalAccessible (endpointMap K) (constantMapNatural K)
  exact Functor.isCardinalAccessible_of_natIso (sigmaPullbackIso K).symm Cardinal.aleph0

/-- The source's finite simplicial sets satisfy the required presentability premise. -/
theorem sigmaFunctor_finite_isCardinalAccessible (K : SSet.{u}) [K.Finite] :
    (sigmaFunctor K).IsCardinalAccessible Cardinal.aleph0.{u} :=
  sigmaFunctor_isCardinalAccessible K

end DaggerModels.OriginalOrdinaryGraphSigmaFunctor
