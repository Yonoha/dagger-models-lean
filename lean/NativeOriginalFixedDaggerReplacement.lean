import NativeFixedDaggerIsomorphismPart
import OriginalFixedObjectLegacyDaggerEquivalence

/-! Reuse the EXACT original fixed-object R through the identity-on-enrichment presentation.
No replacement functor or unit is changed; both are the original legacy R, transported back.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectLegacyDaggerEquivalence
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
attribute [local instance] DaggerFixedCategoryModel.modelCategory
universe u
namespace DaggerNativeOriginalFixedDaggerReplacement
noncomputable section

theorem roundtrip_hom {O : Type u} {C D : FixedDaggerSimplicialCat O} (F : C ⟶ D) :
    toLegacyHom (fromLegacyHom F) = F := by
  rcases F with ⟨⟨⟨obj, map, map_id, map_comp⟩, map_dagger⟩, h⟩
  cases h
  rfl

theorem fromLegacy_weak {O : Type u} {C D : FixedDaggerSimplicialCat O} (F : C ⟶ D)
    [WeakEquivalence F] : WeakEquivalence (fromLegacyHom F) := by
  rw [weakEquivalence_iff]
  change weakEquivalences (FixedDaggerSimplicialCat O) (toLegacyHom (fromLegacyHom F))
  rw [roundtrip_hom]
  exact (weakEquivalence_iff F).mp inferInstance

theorem fromLegacy_fibration {O : Type u} {C D : FixedDaggerSimplicialCat O} (F : C ⟶ D)
    [Fibration F] : Fibration (fromLegacyHom F) := by
  rw [fibration_iff]
  change fibrations (FixedDaggerSimplicialCat O) (toLegacyHom (fromLegacyHom F))
  rw [roundtrip_hom]
  exact (fibration_iff F).mp inferInstance

theorem fromLegacy_fibrant {O : Type u} (C : FixedDaggerSimplicialCat O) [IsFibrant C] :
    IsFibrant (fromLegacyObject C) := by
  letI : (fromLegacyFunctor O).IsRightAdjoint :=
    (legacyDaggerEquivalence O).toAdjunction.isRightAdjoint
  have : Fibration ((fromLegacyFunctor O).map (terminal.from C)) :=
    fromLegacy_fibration (terminal.from C)
  exact (isFibrant_iff_of_isTerminal ((fromLegacyFunctor O).map (terminal.from C))
    (IsTerminal.isTerminalObj (fromLegacyFunctor O) _ terminalIsTerminal)).mpr inferInstance

def replacement (R : FunctorialFibrantReplacement.{u}) :
    FixedDaggerCategory DaggerUnitaryInterval.Vertex ⥤
      FixedDaggerCategory DaggerUnitaryInterval.Vertex :=
  toLegacyFunctor _ ⋙ R.functor ⋙ fromLegacyFunctor _

def unit (R : FunctorialFibrantReplacement.{u})
    (C : FixedDaggerCategory DaggerUnitaryInterval.Vertex) : C ⟶ (replacement R).obj C :=
  fromLegacyHom (R.unit.app (toLegacyObject C))

theorem unit_weak (R : FunctorialFibrantReplacement.{u})
    (C : FixedDaggerCategory DaggerUnitaryInterval.Vertex) : WeakEquivalence (unit R C) := by
  have := R.weakEquivalence (toLegacyObject C)
  exact fromLegacy_weak (R.unit.app (toLegacyObject C))

theorem replacement_fibrant (R : FunctorialFibrantReplacement.{u})
    (C : FixedDaggerCategory DaggerUnitaryInterval.Vertex) :
    IsFibrant ((replacement R).obj C) := by
  have := R.fibrant (toLegacyObject C)
  exact fromLegacy_fibrant (R.functor.obj (toLegacyObject C))

theorem unit_natural (R : FunctorialFibrantReplacement.{u})
    {C D : FixedDaggerCategory DaggerUnitaryInterval.Vertex} (F : C ⟶ D) :
    F ≫ unit R D = unit R C ≫ (replacement R).map F := by
  have h := congrArg (fromLegacyFunctor DaggerUnitaryInterval.Vertex).map
    (R.unit.naturality (toLegacyHom F))
  simpa only [Functor.map_comp] using h

end
end DaggerNativeOriginalFixedDaggerReplacement
