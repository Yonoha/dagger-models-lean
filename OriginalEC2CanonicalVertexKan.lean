import OriginalEC2CanonicalVertexSubcomplex
import OriginalFullVertexSubcomplexKan

/-!
# Functorial canonical-vertex Kan subcomplex

The original constant vertices select a full Kan subcomplex of the literal
singular equivariant mapping object. This point-set functor is an input to
the manuscript's unitary-core construction after a dagger Kan core is supplied;
no maximal Kan core or derived recognition is assumed here.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial
open DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalFullVertexSubcomplex
open DaggerOriginalEC2CanonicalVertexSubcomplex

universe u

namespace DaggerOriginalEC2CanonicalVertexKan

noncomputable section

/-- The actual canonical-vertex full subcomplex is Kan. -/
instance canonicalVertexSubcomplex_kan (K : DaggerSSet.{u}) :
    SSet.KanComplex ((canonicalVertexSubcomplex K).toSSet) := by
  have : SSet.KanComplex (daggerHomotopyFixedPointFunctor.obj K) :=
    mappingSing_kan (realizedContinuousActionFunctor.obj K)
  change SSet.KanComplex
    (fullVertexSubcomplex (daggerHomotopyFixedPointFunctor.obj K) (canonicalVertices K) : SSet)
  infer_instance

/-- Restricting the original mapping functor to exactly the canonical vertices. -/
def canonicalVertexFunctor : DaggerSSet.{u} ⥤ SSet.{u} where
  obj K := (canonicalVertexSubcomplex K).toSSet
  map := canonicalVertexMap
  map_id K := by
    apply NatTrans.ext
    funext n s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (daggerHomotopyFixedPointFunctor.map_id K) n) s.1
  map_comp f g := by
    apply NatTrans.ext
    funext n s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app
      (daggerHomotopyFixedPointFunctor.map_comp f g) n) s.1

/-- The inclusions preserve the specified actual equivariant mapping functor. -/
def canonicalVertexInclusion : canonicalVertexFunctor.{u} ⟶
    daggerHomotopyFixedPointFunctor.{u} where
  app K := (canonicalVertexSubcomplex K).ι
  naturality _ _ _ := rfl

end

end DaggerOriginalEC2CanonicalVertexKan
