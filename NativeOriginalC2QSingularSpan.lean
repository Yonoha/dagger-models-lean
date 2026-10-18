import ActualQKanNaturalComparisons
import NativeOriginalC2RealizationMapping

/-! Reuse BOTH actual old Q-cotensor weak maps with their ORIGINAL C2 target actions. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerSSetGluing DaggerBisimplicialDiagonal
open DaggerOriginalCounitRightConeQFunctor DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualQKanCotensorComparison DaggerActualQKanNaturalComparisons
open DaggerActualQSingularCotensorExchangeIso DaggerNativeOriginalC2RealizationMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalC2QSingularSpan
noncomputable section

def mixedDiagramFunctor : SSet.{u} ⥤ SimplicialObject SSet.{u} where
  obj := mixed
  map := mixedMap
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (ihom (QFunctor.obj n.unop)).map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (ihom (QFunctor.obj n.unop)).map_comp f g

def mixedFunctor : SSet.{u} ⥤ SSet.{u} := mixedDiagramFunctor ⋙ diagonalFunctor

def mixedAction (A : Action SSet.{u} C2.{u}) : Action SSet.{u} C2.{u} :=
  (mixedFunctor.mapAction C2.{u}).obj A

def singularAction (A : Action SSet.{u} C2.{u}) : Action SSet.{u} C2.{u} :=
  (singular.mapAction C2.{u}).obj A

/-- This is exactly the OLD constants map into its OLD mixed cotensor diagonal. -/
def constantsAction (A : Action SSet.{u} C2.{u}) : A ⟶ mixedAction A where
  hom := diagMap (DaggerActualQKanCotensorComparison.constants A.V)
  comm g := constants_naturality (A.ρ g).asHom

/-- This is exactly the OTHER OLD weak leg, with the SAME mixed diagonal endpoint. -/
def singularActionComparison (A : Action SSet.{u} C2.{u}) :
    singularAction A ⟶ mixedAction A where
  hom := singularComparison A.V
  comm g := singularComparison_naturality (A.ρ g).asHom

theorem constantsAction_weak (A : Action SSet.{u} C2.{u}) [A.V.KanComplex] :
    WeakEquivalence (constantsAction A).hom :=
  (weakEquivalence_iff_GW _).mpr (diagonal_constants_GW A.V)

theorem singularActionComparison_weak (A : Action SSet.{u} C2.{u}) [A.V.KanComplex] :
    WeakEquivalence (singularActionComparison A).hom :=
  (weakEquivalence_iff_GW _).mpr (singularComparison_GW A.V)

theorem constantsAction_naturality {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B) :
    f ≫ constantsAction B = constantsAction A ≫ (mixedFunctor.mapAction C2.{u}).map f := by
  apply Action.hom_ext
  exact constants_naturality f.hom

theorem singularActionComparison_naturality {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B) :
    (singular.mapAction C2.{u}).map f ≫ singularActionComparison B =
      singularActionComparison A ≫ (mixedFunctor.mapAction C2.{u}).map f := by
  apply Action.hom_ext
  exact singularComparison_naturality f.hom

def realizedConstants (A : Action SSet.{u} C2.{u}) :
    mappingFunctor.obj A ⟶ mappingFunctor.obj (mixedAction A) :=
  mappingFunctor.map (constantsAction A)

def realizedSingularComparison (A : Action SSet.{u} C2.{u}) :
    mappingFunctor.obj (singularAction A) ⟶ mappingFunctor.obj (mixedAction A) :=
  mappingFunctor.map (singularActionComparison A)

theorem realizedConstants_weak (A : Action SSet.{u} C2.{u}) [A.V.KanComplex] :
    WeakEquivalence (realizedConstants A) := by
  have : WeakEquivalence (constantsAction A).hom := constantsAction_weak A
  exact mapping_map_weak _

theorem realizedSingularComparison_weak (A : Action SSet.{u} C2.{u}) [A.V.KanComplex] :
    WeakEquivalence (realizedSingularComparison A) := by
  have : WeakEquivalence (singularActionComparison A).hom := singularActionComparison_weak A
  exact mapping_map_weak _

end
end DaggerNativeOriginalC2QSingularSpan
