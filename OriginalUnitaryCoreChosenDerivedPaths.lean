import OriginalUnitaryCorePathFibers
import OriginalStrictPathFiberReplacement

/-!
# A single functorial point-replacement model for original unitary-core paths

One native functorial factorization supplies the replacements of the same
canonical endpoint pairs and their transition map. The actual inclusion
induces a weak equivalence of these replacement fibers. Its comparison with
the strict path-fiber isomorphism commutes on both pullback legs. This does
not assume or prove equivariant derived mapping-space recognition.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial Opposite DaggerModels
open MonoidalCategory MonoidalClosed MorphismProperty
open DaggerOriginalFullVertexSubcomplex DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices DaggerOriginalUnitaryCorePathFibers
open DaggerOriginalStrictPathFiberReplacement
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalUnitaryCoreChosenDerivedPaths

noncomputable section

/-- One native factorization datum is used for every original endpoint point arrow. -/
def pointFactorization : FunctorialFactorizationData
    (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) :=
  functorialFactorizationData _ _

variable (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌))

/-- The source point uses the original canonical unitary vertices. -/
def sourcePoint : (Δ[0] : SSet.{u}) ⟶ (unitaryCore X) ⊗ (unitaryCore X) :=
  SSet.yonedaEquiv.symm (canonicalUnitaryVertex X x, canonicalUnitaryVertex X y)

/-- The target point retains the same two original constant homotopy-fixed vertices. -/
def targetPoint : (Δ[0] : SSet.{u}) ⟶
    (unitaryCoreAmbientFunctor.obj X) ⊗ (unitaryCoreAmbientFunctor.obj X) :=
  SSet.yonedaEquiv.symm ((canonicalUnitaryVertex X x).val, (canonicalUnitaryVertex X y).val)

/-- The actual original inclusion on both endpoint coordinates. -/
def endpointInclusion : (unitaryCore X) ⊗ (unitaryCore X) ⟶
    (unitaryCoreAmbientFunctor.obj X) ⊗ (unitaryCoreAmbientFunctor.obj X) :=
  (unitaryCoreInclusion.app X) ⊗ₘ (unitaryCoreInclusion.app X)

/-- The point-arrow square retains identity on the original parameter point. -/
def pointSquare : Arrow.mk (sourcePoint X x y) ⟶ Arrow.mk (targetPoint X x y) :=
  Arrow.homMk (𝟙 (Δ[0] : SSet.{u})) (endpointInclusion X) (by rfl)

/-- The one chosen source replacement of the original canonical endpoint pair. -/
def sourceReplacement : SSet.{u} := pointFactorization.Z.obj (Arrow.mk (sourcePoint X x y))

/-- The same datum chooses the ambient replacement of that same canonical endpoint pair. -/
def targetReplacement : SSet.{u} := pointFactorization.Z.obj (Arrow.mk (targetPoint X x y))

def sourceLeft : (Δ[0] : SSet.{u}) ⟶ sourceReplacement X x y :=
  pointFactorization.i.app (Arrow.mk (sourcePoint X x y))

def sourceRight : sourceReplacement X x y ⟶ (unitaryCore X) ⊗ (unitaryCore X) :=
  pointFactorization.p.app (Arrow.mk (sourcePoint X x y))

def targetLeft : (Δ[0] : SSet.{u}) ⟶ targetReplacement X x y :=
  pointFactorization.i.app (Arrow.mk (targetPoint X x y))

def targetRight : targetReplacement X x y ⟶
    (unitaryCoreAmbientFunctor.obj X) ⊗ (unitaryCoreAmbientFunctor.obj X) :=
  pointFactorization.p.app (Arrow.mk (targetPoint X x y))

/-- The transition is forced by the same datum applied to the actual original point square. -/
def replacementMap : sourceReplacement X x y ⟶ targetReplacement X x y :=
  pointFactorization.Z.map (pointSquare X x y)

theorem source_fac : sourceLeft X x y ≫ sourceRight X x y = sourcePoint X x y :=
  pointFactorization.fac_app (f := Arrow.mk (sourcePoint X x y))

theorem target_fac : targetLeft X x y ≫ targetRight X x y = targetPoint X x y :=
  pointFactorization.fac_app (f := Arrow.mk (targetPoint X x y))

theorem left_compat : sourceLeft X x y ≫ replacementMap X x y = targetLeft X x y := by
  have h := (pointFactorization.i.naturality (pointSquare X x y)).symm
  simpa [sourceLeft, targetLeft, replacementMap, pointSquare] using h

theorem right_compat : sourceRight X x y ≫ endpointInclusion X =
    replacementMap X x y ≫ targetRight X x y := by
  simp [sourceRight, targetRight, replacementMap, pointSquare]

theorem source_left_weakEquivalence : WeakEquivalence (sourceLeft X x y) :=
  ((mem_trivialCofibrations_iff _).1
    (pointFactorization.hi (Arrow.mk (sourcePoint X x y)))).2

theorem target_left_weakEquivalence : WeakEquivalence (targetLeft X x y) :=
  ((mem_trivialCofibrations_iff _).1
    (pointFactorization.hi (Arrow.mk (targetPoint X x y)))).2

theorem source_right_fibration : Fibration (sourceRight X x y) :=
  (HomotopicalAlgebra.fibration_iff _).2
    (pointFactorization.hp (Arrow.mk (sourcePoint X x y)))

theorem target_right_fibration : Fibration (targetRight X x y) :=
  (HomotopicalAlgebra.fibration_iff _).2
    (pointFactorization.hp (Arrow.mk (targetPoint X x y)))

/-- The original strict unitary fiber maps to its one chosen replacement fiber. -/
def sourceStrictComparison :
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet) ⟶
    pullback (unitaryCore X).pathEv₀₁ (sourceRight X x y) :=
  comparison (unitaryCore X).pathEv₀₁
    (canonicalUnitaryVertex X x, canonicalUnitaryVertex X y)
    (sourceLeft X x y) (sourceRight X x y) (source_fac X x y)

/-- The same comparison uses the original ambient strict fiber at those same two vertices. -/
def targetStrictComparison :
    (strictPathFiber (unitaryCoreAmbientFunctor.obj X)
      (canonicalUnitaryVertex X x).val (canonicalUnitaryVertex X y).val : SSet) ⟶
    pullback (unitaryCoreAmbientFunctor.obj X).pathEv₀₁ (targetRight X x y) :=
  comparison (unitaryCoreAmbientFunctor.obj X).pathEv₀₁
    ((canonicalUnitaryVertex X x).val, (canonicalUnitaryVertex X y).val)
    (targetLeft X x y) (targetRight X x y) (target_fac X x y)

/-- The literal original inclusion-induced map of the two chosen replacement fibers. -/
def chosenDerivedPathMap :
    pullback (unitaryCore X).pathEv₀₁ (sourceRight X x y) ⟶
    pullback (unitaryCoreAmbientFunctor.obj X).pathEv₀₁ (targetRight X x y) :=
  pullback.map _ _ _ _ ((ihom Δ[1]).map (unitaryCoreInclusion.app X))
    (replacementMap X x y) (endpointInclusion X)
    (pathEv_pair_natural (unitaryCoreInclusion.app X)).symm (right_compat X x y)

/-- The actual strict-fiber isomorphism and both chosen comparison maps form a commuting square.
-/
theorem chosenComparison_naturality :
    sourceStrictComparison X x y ≫ chosenDerivedPathMap X x y =
      (unitaryCorePathFiberIso X x y).hom ≫ targetStrictComparison X x y := by
  unfold sourceStrictComparison targetStrictComparison chosenDerivedPathMap
  apply comparison_naturality
  · exact left_compat X x y
  · change strictPathFiberMap (unitaryCoreInclusion.app X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) ≫ _ = _
    dsimp only [strictPathFiberMap]
    exact SSet.Subcomplex.lift_ι _ _

theorem sourceStrictComparison_weakEquivalence :
    WeakEquivalence (sourceStrictComparison X x y) := by
  have : Fibration (unitaryCore X).pathEv₀₁ := unitaryCorePathEndpoint_fibration X
  have : WeakEquivalence (sourceLeft X x y) := source_left_weakEquivalence X x y
  exact comparison_weakEquivalence _ _ _ _ _

theorem targetStrictComparison_weakEquivalence :
    WeakEquivalence (targetStrictComparison X x y) := by
  have : Fibration (unitaryCoreAmbientFunctor.obj X).pathEv₀₁ :=
    unitaryCoreAmbientPathEndpoint_fibration X
  have : WeakEquivalence (targetLeft X x y) := target_left_weakEquivalence X x y
  exact comparison_weakEquivalence _ _ _ _ _

/-- The original inclusion induces a weak equivalence in this explicit replacement-fiber model.
-/
theorem chosenDerivedPathMap_weakEquivalence :
    WeakEquivalence (chosenDerivedPathMap X x y) := by
  have : WeakEquivalence (unitaryCorePathFiberIso X x y).hom := inferInstance
  have : WeakEquivalence (targetStrictComparison X x y) :=
    targetStrictComparison_weakEquivalence X x y
  have : WeakEquivalence (sourceStrictComparison X x y ≫ chosenDerivedPathMap X x y) := by
    rw [chosenComparison_naturality]
    infer_instance
  have : WeakEquivalence (sourceStrictComparison X x y) :=
    sourceStrictComparison_weakEquivalence X x y
  exact weakEquivalence_of_precomp (sourceStrictComparison X x y) (chosenDerivedPathMap X x y)

end

end DaggerOriginalUnitaryCoreChosenDerivedPaths
