import NativeAmbientDaggerMappingTargetWeak
import NativeAmbientDaggerMappingKan
import NativeOriginalFixedRWeakPreservation

/-! The SAME original enriched mapping functor after the EXACT original R.
It is Kan and weak-invariant on ALL targets; on native fibrant targets its unit is weak.
The resulting ordinary localization functor is constructed without claiming a derived universal
property that has not yet been checked.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeOriginalFixedDaggerReplacement
open DaggerNativeAmbientDaggerMappingTargetWeak
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeOriginalRReplacedMapping
noncomputable section

abbrev fixedWeak : MorphismProperty
    (FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) := weakEquivalences _

abbrev kanWeak : MorphismProperty SSet.{u} := weakEquivalences _

def functor (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) :
    FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u} ⥤ SSet.{u} :=
  replacement R ⋙ targetMappingFunctor A

theorem obj_kan (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (C : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) :
    ((functor R A).obj C).KanComplex := by
  have := replacement_fibrant R C
  exact DaggerNativeAmbientDaggerMappingKan.mapping_kan A _

theorem map_weak (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    {C D : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}} (F : C ⟶ D)
    [WeakEquivalence F] : WeakEquivalence ((functor R A).map F) := by
  have := replacement_fibrant R C
  have := replacement_fibrant R D
  have := DaggerNativeOriginalFixedRWeakPreservation.map_weak R F
  exact mappingTarget_weak A ((replacement R).map F)

def unitMap (R : FunctorialFibrantReplacement.{u})
    (A C : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) :
    (A ⟶[SSet.{u}] C) ⟶ (functor R A).obj C :=
  eHomWhiskerLeft SSet A (unit R C)

theorem unitMap_weak (R : FunctorialFibrantReplacement.{u})
    (A C : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u})
    [IsCofibrant A] [IsFibrant C] : WeakEquivalence (unitMap R A C) := by
  have := replacement_fibrant R C
  have := unit_weak R C
  exact mappingTarget_weak A (unit R C)

theorem unitMap_natural (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u})
    {C D : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}} (F : C ⟶ D) :
    eHomWhiskerLeft SSet A F ≫ unitMap R A D = unitMap R A C ≫ (functor R A).map F := by
  change eHomWhiskerLeft SSet A F ≫ eHomWhiskerLeft SSet A (unit R D) =
    eHomWhiskerLeft SSet A (unit R C) ≫ eHomWhiskerLeft SSet A ((replacement R).map F)
  rw [← eHomWhiskerLeft_comp, ← eHomWhiskerLeft_comp]
  exact congrArg (eHomWhiskerLeft SSet A) (unit_natural R F)

theorem inverts (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A] :
    fixedWeak.{u}.IsInvertedBy (functor R A ⋙ kanWeak.Q) := by
  intro C D F hF
  have : WeakEquivalence F := (weakEquivalence_iff F).mpr hF
  have := map_weak R A F
  exact Localization.inverts kanWeak.Q kanWeak ((functor R A).map F)
    (mem_weakEquivalences _)

def localized (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A] :
    fixedWeak.{u}.Localization ⥤ kanWeak.{u}.Localization :=
  Localization.lift (functor R A ⋙ kanWeak.Q) (inverts R A) fixedWeak.Q

def factorizationIso (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A] :
    fixedWeak.Q ⋙ localized R A ≅ functor R A ⋙ kanWeak.Q :=
  Localization.fac (functor R A ⋙ kanWeak.Q) (inverts R A) fixedWeak.Q

end
end DaggerNativeOriginalRReplacedMapping
