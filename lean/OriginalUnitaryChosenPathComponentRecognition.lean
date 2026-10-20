import OriginalUnitaryCoreChosenDerivedPaths
import OriginalReplacementPathFiberNonemptiness
import OriginalUnitaryCoreComponentSurjectivity
import OriginalUnitaryMappingWeakEquivalenceRecognition

/-!
# Original unitary components recognized by the actual chosen path fibers

The same fixed functorial point factorization gives actual unitary and
ambient replacement path fibers. Equality of the original canonical
components is equivalent to existence of a vertex in either exact fiber.
For the same original dagger map, unitary component coverage is therefore
equivalent to existence of these actual chosen paths to every target
canonical vertex. No interval-to-rigidification comparison is assumed here.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory
open DaggerOriginalFullVertexSubcomplex DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices DaggerOriginalUnitaryCorePathFibers
open DaggerOriginalUnitaryCoreChosenDerivedPaths
open DaggerOriginalReplacementPathFiberNonemptiness DaggerOriginalStrictPathFiberVertices
open DaggerOriginalUnitaryCoreComponentSurjectivity
open DaggerOriginalInnerHornFillers DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryMappingWeakEquivalenceRecognition
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalUnitaryChosenPathComponentRecognition

noncomputable section

/-- The actual replacement pullback for the original canonical unitary endpoints. -/
def chosenUnitaryPath (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{u} :=
  pullback (unitaryCore X).pathEv₀₁ (sourceRight X x y)

/-- The actual ambient replacement pullback at the same original constant endpoints. -/
def chosenAmbientPath (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{u} :=
  pullback (unitaryCoreAmbientFunctor.obj X).pathEv₀₁ (targetRight X x y)

/-- The same chosen unitary path fiber is native Kan. -/
theorem chosenUnitaryPath_kan (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    (chosenUnitaryPath X x y).KanComplex := by
  haveI := unitaryCore_kan X
  haveI := source_right_fibration X x y
  exact replacementPathFiber_fibrant (sourceRight X x y)

/-- The same chosen ambient path fiber is native Kan. -/
theorem chosenAmbientPath_kan (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    (chosenAmbientPath X x y).KanComplex := by
  haveI := unitaryCoreAmbient_kan X
  haveI := target_right_fibration X x y
  exact replacementPathFiber_fibrant (targetRight X x y)

/-- Original canonical component equality is nonemptiness of the exact strict unitary fiber. -/
theorem components_eq_iff_strictPath_vertex (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) ↔
      Nonempty ((strictPathFiber (unitaryCore X)
        (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet).obj (op ⦋0⦌)) := by
  haveI := unitaryCore_kan X
  exact (strictPathFiber_vertex_nonempty_iff (unitaryCore X) _ _).symm

/-- Original canonical component equality is nonemptiness of the same chosen unitary fiber. -/
theorem components_eq_iff_chosenUnitaryPath_vertex (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) ↔
      Nonempty ((chosenUnitaryPath X x y).obj (op ⦋0⦌)) := by
  haveI := unitaryCore_kan X
  haveI := source_left_weakEquivalence X x y
  haveI := source_right_fibration X x y
  exact (replacementPathFiber_vertex_nonempty_iff (canonicalUnitaryVertex X x)
    (canonicalUnitaryVertex X y) (sourceLeft X x y) (sourceRight X x y)
      (source_fac X x y)).symm

/-- The verified original inclusion comparison preserves existence of chosen path vertices. -/
theorem chosen_path_vertex_nonempty_iff (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    Nonempty ((chosenUnitaryPath X x y).obj (op ⦋0⦌)) ↔
      Nonempty ((chosenAmbientPath X x y).obj (op ⦋0⦌)) := by
  haveI := chosenUnitaryPath_kan X x y
  haveI := chosenAmbientPath_kan X x y
  haveI := chosenDerivedPathMap_weakEquivalence X x y
  exact vertices_nonempty_iff_of_weakEquivalence (chosenDerivedPathMap X x y)

/-- Original canonical component equality is nonemptiness of the same chosen ambient fiber. -/
theorem components_eq_iff_chosenAmbientPath_vertex (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) ↔
      Nonempty ((chosenAmbientPath X x y).obj (op ⦋0⦌)) :=
  (components_eq_iff_chosenUnitaryPath_vertex X x y).trans
    (chosen_path_vertex_nonempty_iff X x y)

/-- Unitariy component coverage is precisely existence of chosen original paths to all target
 canonical vertices. -/
theorem unitary_components_surjective_iff_chosenPaths {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) ↔
      ∀ y : Y.toSSet.obj (op ⦋0⦌), ∃ x : X.toSSet.obj (op ⦋0⦌),
        Nonempty ((chosenUnitaryPath Y (f.hom.app (op ⦋0⦌) x) y).obj (op ⦋0⦌)) := by
  rw [unitary_pi0_surjective_iff_canonical]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, (components_eq_iff_chosenUnitaryPath_vertex Y _ y).mp hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, (components_eq_iff_chosenUnitaryPath_vertex Y _ y).mpr hx⟩

/-- The same coverage condition can be stated using the actual chosen ambient fibers. -/
theorem unitary_components_surjective_iff_chosenAmbientPaths {X Y : DaggerSSet.{u}}
    (f : X ⟶ Y) :
    Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) ↔
      ∀ y : Y.toSSet.obj (op ⦋0⦌), ∃ x : X.toSSet.obj (op ⦋0⦌),
        Nonempty ((chosenAmbientPath Y (f.hom.app (op ⦋0⦌) x) y).obj (op ⦋0⦌)) := by
  rw [unitary_pi0_surjective_iff_canonical]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, (components_eq_iff_chosenAmbientPath_vertex Y _ y).mp hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, (components_eq_iff_chosenAmbientPath_vertex Y _ y).mpr hx⟩

/-- Actual original mapping weak equivalences and actual chosen unitary path coverage imply
 weak equivalence of the same original unitary map. -/
theorem unitaryCore_map_weakEquivalence_of_mappingWeak_and_chosenPaths
    {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X.toSSet) (hY : innerHornFillers Y.toSSet)
    (hmap : ∀ x y : X.toSSet.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f.hom x y))
    (hpaths : ∀ y : Y.toSSet.obj (op ⦋0⦌), ∃ x : X.toSSet.obj (op ⦋0⦌),
      Nonempty ((chosenUnitaryPath Y (f.hom.app (op ⦋0⦌) x) y).obj (op ⦋0⦌))) :
    WeakEquivalence (unitaryCoreFunctor.map f) :=
  unitaryCore_map_weakEquivalence_of_mappingWeak_and_unitaryComponents f hX hY hmap
    ((unitary_components_surjective_iff_chosenPaths f).mpr hpaths)

end

end DaggerOriginalUnitaryChosenPathComponentRecognition
