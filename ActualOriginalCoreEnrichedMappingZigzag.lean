import NativeOriginalRReplacedMapping
import ActualOriginalRPartMappingKan
import ActualOriginalCoreCompletionFibrancy

/-! Apply the EXACT original R and the SAME whole enriched mapping functor to CP211.
For EVERY cofibrant fixed-object source, the ORIGINAL R groupoidal part and ORIGINAL completed
core have an explicit FIVE-ARROW zigzag of Kan weak maps. No interval/path dictionary is assumed.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerActualOriginalFixedRCoreZigzag
open DaggerActualOriginalBipointedRCoreZigzag DaggerNativeOriginalRReplacedMapping
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualOriginalCoreEnrichedMappingZigzag
noncomputable section

def leftUnit (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :=
  unitMap R A (replacedPart R X (labels X x y))

def postMap (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :=
  (functor R A).map (post R X (labels X x y))

def firstMap (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) (X : DaggerSSet.{u})
    [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :=
  (functor R A).map (DaggerActualFixedDaggerCoreComparison.comparison X
    (coreLabels X x y) (labels X x y) (labels_compatible X x y))

def completionMap (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) (X : DaggerSSet.{u})
    [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :=
  (functor R A).map (DaggerActualDaggerCoreEndpointRestriction.comparison X x y)

def rightUnit (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) (X : DaggerSSet.{u})
    [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :=
  unitMap R A (DaggerActualDaggerCoreEndpointRestriction.target X x y)

theorem all_maps_weak (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (leftUnit R A X x y) ∧ WeakEquivalence (postMap R A X x y) ∧
    WeakEquivalence (firstMap R A X x y) ∧ WeakEquivalence (completionMap R A X x y) ∧
    WeakEquivalence (rightUnit R A X x y) := by
  have := DaggerActualOriginalRPartMappingKan.replacedPart_fibrant R X (labels X x y)
  have := DaggerActualOriginalCoreCompletionFibrancy.target_fibrant X x y
  have hw := DaggerActualOriginalBipointedRCoreZigzag.all_three_arrows_weak R X x y
  have : WeakEquivalence (post R X (labels X x y)) := hw.1
  have : WeakEquivalence (DaggerActualFixedDaggerCoreComparison.comparison X
      (coreLabels X x y) (labels X x y) (labels_compatible X x y)) := hw.2.1
  have : WeakEquivalence (DaggerActualDaggerCoreEndpointRestriction.comparison X x y) := hw.2.2
  exact ⟨unitMap_weak R A _, map_weak R A _, map_weak R A _, map_weak R A _, unitMap_weak R A _⟩

theorem all_nodes_kan (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    (A ⟶[SSet.{u}] replacedPart R X (labels X x y)).KanComplex ∧
    ((functor R A).obj (replacedPart R X (labels X x y))).KanComplex ∧
    ((functor R A).obj (DaggerNativeFixedDaggerIsomorphismPart.part
      (ambient X (labels X x y)))).KanComplex ∧
    ((functor R A).obj (DaggerActualDaggerCoreEndpointRestriction.source X x y)).KanComplex ∧
    ((functor R A).obj (DaggerActualDaggerCoreEndpointRestriction.target X x y)).KanComplex ∧
    (A ⟶[SSet.{u}] DaggerActualDaggerCoreEndpointRestriction.target X x y).KanComplex := by
  have := DaggerActualOriginalCoreCompletionFibrancy.target_fibrant X x y
  exact ⟨DaggerActualOriginalRPartMappingKan.mapping_kan A R X _, obj_kan R A _, obj_kan R A _,
    obj_kan R A _, obj_kan R A _, DaggerNativeAmbientDaggerMappingKan.mapping_kan A _⟩

def kanLocalizationIso (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    kanWeak.Q.obj (A ⟶[SSet.{u}] DaggerActualDaggerCoreEndpointRestriction.target X x y) ≅
      kanWeak.Q.obj (A ⟶[SSet.{u}] replacedPart R X (labels X x y)) := by
  have hw := all_maps_weak R A X x y
  have : IsIso (kanWeak.Q.map (leftUnit R A X x y)) :=
    Localization.inverts kanWeak.Q kanWeak _ ((weakEquivalence_iff _).mp hw.1)
  have : IsIso (kanWeak.Q.map (postMap R A X x y)) :=
    Localization.inverts kanWeak.Q kanWeak _ ((weakEquivalence_iff _).mp hw.2.1)
  have : IsIso (kanWeak.Q.map (firstMap R A X x y)) :=
    Localization.inverts kanWeak.Q kanWeak _ ((weakEquivalence_iff _).mp hw.2.2.1)
  have : IsIso (kanWeak.Q.map (completionMap R A X x y)) :=
    Localization.inverts kanWeak.Q kanWeak _ ((weakEquivalence_iff _).mp hw.2.2.2.1)
  have : IsIso (kanWeak.Q.map (rightUnit R A X x y)) :=
    Localization.inverts kanWeak.Q kanWeak _ ((weakEquivalence_iff _).mp hw.2.2.2.2)
  exact asIso (kanWeak.Q.map (rightUnit R A X x y)) ≪≫
    (asIso (kanWeak.Q.map (completionMap R A X x y))).symm ≪≫
    asIso (kanWeak.Q.map (firstMap R A X x y)) ≪≫
    asIso (kanWeak.Q.map (postMap R A X x y)) ≪≫
    (asIso (kanWeak.Q.map (leftUnit R A X x y))).symm

end
end DaggerActualOriginalCoreEnrichedMappingZigzag
