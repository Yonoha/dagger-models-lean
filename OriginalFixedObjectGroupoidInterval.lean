import OriginalFixedObjectCotensorPoints

/-!
# The interval diagram of the original fixed-object strict groupoids

Use the actual cotensor by the standard simplicial interval. Both endpoint
evaluations and the constant map are full natural transformations in the
original fixed-object groupoid categories. On every original Hom, their paired
composite is exactly the diagonal. This diagram does not yet assert the model
path-object weak-equivalence and fibration conditions.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectCotensorPoints
universe u

namespace DaggerOriginalFixedObjectGroupoidInterval

noncomputable section

/-- Each actual interval vertex gives a global point in all simplicial degrees. -/
def intervalPoint (v : Fin 2) : 𝟙_ SSet.{u} ⟶ Δ[1] where
  app n _ := SSet.stdSimplex.const 1 v n
  naturality _ _ _ := by
    funext p
    rfl

/-- The original strict interval cotensor on exactly O. -/
def intervalFunctor (O : Type u) : FixedStrictGroupoids O ⥤ FixedStrictGroupoids O :=
  strictCotensorFunctor O Δ[1]

/-- Constants form a full natural transformation in the original strict groupoid category. -/
def constantNat (O : Type u) : 𝟭 (FixedStrictGroupoids O) ⟶ intervalFunctor O where
  app C := strictConstant Δ[1] C
  naturality _ _ F := ObjectProperty.hom_ext _ (constant_natural Δ[1] F.hom)

/-- Either endpoint forms a full natural transformation on the original strict groupoids. -/
def evaluationNat (O : Type u) (v : Fin 2) : intervalFunctor O ⟶ 𝟭 (FixedStrictGroupoids O)
    where
  app C := strictEvaluation (intervalPoint v) C
  naturality _ _ F := ObjectProperty.hom_ext _ (evaluation_natural (intervalPoint v) F.hom)

/-- The complete natural-transformation composite is the identity at either endpoint. -/
theorem constantNat_evaluationNat (O : Type u) (v : Fin 2) :
    constantNat O ≫ evaluationNat O v = 𝟙 (𝟭 (FixedStrictGroupoids O)) := by
  apply NatTrans.ext
  funext C
  exact strictConstant_evaluation (intervalPoint v) C

/-- The actual strict dagger interval cotensor retains exactly O. -/
def daggerIntervalFunctor (O : Type u) :
    FixedStrictDaggerGroupoids O ⥤ FixedStrictDaggerGroupoids O :=
  strictDaggerCotensorFunctor O Δ[1]

/-- Dagger constants are a full natural transformation on the original strict dagger category. -/
def daggerConstantNat (O : Type u) :
    𝟭 (FixedStrictDaggerGroupoids O) ⟶ daggerIntervalFunctor O where
  app C := strictDaggerConstant Δ[1] C
  naturality _ _ F := ObjectProperty.hom_ext _ (daggerConstant_natural Δ[1] F.hom)

/-- The endpoint transformations preserve the original dagger in every degree. -/
def daggerEvaluationNat (O : Type u) (v : Fin 2) :
    daggerIntervalFunctor O ⟶ 𝟭 (FixedStrictDaggerGroupoids O) where
  app C := strictDaggerEvaluation (intervalPoint v) C
  naturality _ _ F := ObjectProperty.hom_ext _
    (daggerEvaluation_natural (intervalPoint v) F.hom)

/-- The original dagger interval diagram splits at either endpoint as whole functors. -/
theorem daggerConstantNat_evaluationNat (O : Type u) (v : Fin 2) :
    daggerConstantNat O ≫ daggerEvaluationNat O v = 𝟙 (𝟭 (FixedStrictDaggerGroupoids O)) := by
  apply NatTrans.ext
  funext C
  exact strictDaggerConstant_evaluation (intervalPoint v) C

/-- The native paired endpoint map on an unchanged original Hom simplicial set. -/
def endpointPair (X : SSet.{u}) : (ihom (Δ[1] : SSet.{u})).obj X ⟶ X ⊗ X where
  app n f := ((pointEvaluation (intervalPoint 0) X).app n f,
    (pointEvaluation (intervalPoint 1) X).app n f)
  naturality _ _ i := by
    funext f
    apply Prod.ext
    · exact congrFun ((pointEvaluation (intervalPoint 0) X).naturality i) f
    · exact congrFun ((pointEvaluation (intervalPoint 1) X).naturality i) f

/-- The original interval diagram factors the entire original Hom diagonal. -/
theorem constant_endpointPair (X : SSet.{u}) :
    constantHom Δ[1] X ≫ endpointPair X =
      CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X) := by
  apply NatTrans.ext
  funext n f
  change (X.map (𝟙 n) f, X.map (𝟙 n) f) = (f, f)
  rw [X.map_id]
  rfl

/-- Endpoint pairing is natural for every map of original Hom simplicial sets. -/
theorem endpointPair_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{u})).map f ≫ endpointPair Y = endpointPair X ≫ (f ⊗ₘ f) := by
  apply NatTrans.ext
  funext n g
  rfl

/-- Every original strict groupoid Hom in the interval remains Kan without an extra premise. -/
theorem intervalHom_kan {O : Type u} (C : FixedStrictGroupoids O) (x y : O) :
    ((intervalFunctor O).obj C).obj.enriched.Hom x y |>.KanComplex :=
  fixedStrictHom_kan (strictCotensor Δ[1] C) x y

end

end DaggerOriginalFixedObjectGroupoidInterval
