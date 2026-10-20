import ActualOriginalCoreInclusionUnitaryWeak
import ActualCanonicalDaggerKanCompletionUnitWeak

/-! The SAME original unitary core compared with the FULL completed core nerve.
Both actual dagger arrows and canonical vertices are retained before Kan localization.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerActualDaggerOrdinaryCore DaggerNativeOriginalRReplacedMapping
open DaggerActualCanonicalDaggerKanCompletionUnit
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualOriginalUnitaryCoreCompletionComparison
noncomputable section

def completedNerve (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] : DaggerSSet.{u} :=
  DaggerNerve.daggerCoherentNerve.obj (target (coreDagger X))

def left (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    unitaryCore (coreDagger X) ⟶ unitaryCore X :=
  unitaryCoreFunctor.map (DaggerActualDaggerOrdinaryCoreMaps.inclusion X)

def right (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    unitaryCore (coreDagger X) ⟶ unitaryCore (completedNerve X) :=
  unitaryCoreFunctor.map (unit (coreDagger X))

theorem left_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] : WeakEquivalence (left X) :=
  DaggerActualOriginalCoreInclusionUnitaryWeak.unitary_core_inclusion_weak X

theorem right_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] : WeakEquivalence (right X) := by
  have := coreDagger_kan X
  have := DaggerActualCanonicalDaggerKanCompletionUnitWeak.target_nerve_kan (coreDagger X)
  exact DaggerNativeDaggerKanUnitaryCoreWeak.unitary_map_weak (unit (coreDagger X))
    (DaggerActualCanonicalDaggerKanCompletionUnitWeak.unit_weak (coreDagger X))
    (DaggerActualCanonicalDaggerKanCompletionUnitWeak.unit_vertex_bijective
      (coreDagger X)).surjective

def leftIso (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    kanWeak.Q.obj (unitaryCore (coreDagger X)) ≅ kanWeak.Q.obj (unitaryCore X) :=
  have := left_weak X
  have : IsIso (kanWeak.Q.map (left X)) :=
    Localization.inverts kanWeak.Q kanWeak _ (mem_weakEquivalences _)
  asIso (kanWeak.Q.map (left X))

def rightIso (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    kanWeak.Q.obj (unitaryCore (coreDagger X)) ≅
      kanWeak.Q.obj (unitaryCore (completedNerve X)) :=
  have := right_weak X
  have : IsIso (kanWeak.Q.map (right X)) :=
    Localization.inverts kanWeak.Q kanWeak _ (mem_weakEquivalences _)
  asIso (kanWeak.Q.map (right X))

def comparisonIso (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    kanWeak.Q.obj (unitaryCore X) ≅ kanWeak.Q.obj (unitaryCore (completedNerve X)) :=
  (leftIso X).symm ≪≫ rightIso X

theorem comparison_triangle (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    kanWeak.Q.map (left X) ≫ (comparisonIso X).hom = kanWeak.Q.map (right X) := by
  change (leftIso X).hom ≫ ((leftIso X).inv ≫ (rightIso X).hom) = (rightIso X).hom
  simp only [Iso.hom_inv_id_assoc]

theorem left_vertex (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a : (coreDagger X).toSSet.obj (op ⦋0⦌)) :
    (left X).app (op ⦋0⦌) (canonicalUnitaryVertex (coreDagger X) a) =
      canonicalUnitaryVertex X ((DaggerActualDaggerOrdinaryCoreMaps.inclusion X).hom.app
        (op ⦋0⦌) a) :=
  canonicalUnitaryVertex_naturality (DaggerActualDaggerOrdinaryCoreMaps.inclusion X) a

theorem right_vertex (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a : (coreDagger X).toSSet.obj (op ⦋0⦌)) :
    (right X).app (op ⦋0⦌) (canonicalUnitaryVertex (coreDagger X) a) =
      canonicalUnitaryVertex (completedNerve X) ((unit (coreDagger X)).hom.app (op ⦋0⦌) a) :=
  canonicalUnitaryVertex_naturality (unit (coreDagger X)) a

end
end DaggerActualOriginalUnitaryCoreCompletionComparison
