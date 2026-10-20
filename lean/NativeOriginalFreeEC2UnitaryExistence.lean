import NativeOriginalCompletedCoreUnitaryExistence
import OriginalFixedObjectFreeEC2Mapping
import NativeStrictDaggerObjectRestriction

/-! Exact two-label restriction retains Sigma and the ORIGINAL freeEC2 mapping object. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictDaggerGroupoidMappingAction
open DaggerOriginalStrictDaggerGroupoidDerivedMapping
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction DaggerOriginalEC2SimplicialAction
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectFreeEC2Mapping
open DaggerNativeDaggerObjectRestriction DaggerNativeStrictDaggerObjectRestriction
open DaggerNativeOriginalCompletedCoreUnitaryExistence DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerOriginalFreeEC2DaggerGroupoidComparison
universe u
namespace DaggerNativeOriginalFreeEC2UnitaryExistence
noncomputable section

variable {O : Type u}

def restrictionActionIso (D : DaggerSimplicialCat.{u, u})
    (hD : IsStrictGroupoid D.toSimplicialCat) (θ : O → D.Obj) (i j : O) :
    strictMappingAction (originalDagger (restriction D θ)) (restriction_strict D θ hD) i j ≅
      strictMappingAction D hD (θ i) (θ j) :=
  Action.mkIso (Iso.refl _) (strictMappingActionMap (restriction_strict D θ hD) hD
    (DaggerNativeDaggerRestrictionInclusion.inclusion D θ) i j).comm

theorem restrictionActionIso_hom (D : DaggerSimplicialCat.{u, u})
    (hD : IsStrictGroupoid D.toSimplicialCat) (θ : O → D.Obj) (i j : O) :
    (restrictionActionIso D hD θ i j).hom.hom = 𝟙 _ := rfl

def restrictionDerivedIso (D : DaggerSimplicialCat.{u, u})
    (hD : IsStrictGroupoid D.toSimplicialCat) (θ : O → D.Obj) (i j : O) :
    strictDerivedMapping (originalDagger (restriction D θ)) (restriction_strict D θ hD) i j ≅
      strictDerivedMapping D hD (θ i) (θ j) :=
  (enrichedMappingFunctor simplicialAction).mapIso (restrictionActionIso D hD θ i j)

variable (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet _⦋0⦌)

def freeCompletedIso :
    (freeEC2 ⟶[SSet.{u}] strictCoreTarget X x y) ≅
      strictDerivedMapping (fullCompletion X) (fullCompletion_strict X)
        (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X x)
        (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X y) :=
  freeEC2MappingIso (strictCoreTarget X x y) ≪≫
    restrictionDerivedIso (fullCompletion X) (fullCompletion_strict X)
      (DaggerActualDaggerCoreEndpointRestriction.labels X x y)
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right

theorem free_vertices_iff_original_unitary :
    Nonempty ((freeEC2 ⟶[SSet.{u}] strictCoreTarget X x y) _⦋0⦌) ↔
      SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) := by
  have hi : Nonempty ((freeEC2 ⟶[SSet.{u}] strictCoreTarget X x y) _⦋0⦌) ↔
      Nonempty ((strictDerivedMapping (fullCompletion X) (fullCompletion_strict X)
        (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X x)
        (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X y)) _⦋0⦌) :=
    ⟨fun ⟨v⟩ ↦ ⟨(freeCompletedIso X x y).hom.app (op ⦋0⦌) v⟩,
      fun ⟨v⟩ ↦ ⟨(freeCompletedIso X x y).inv.app (op ⦋0⦌) v⟩⟩
  exact hi.trans (derived_completed_vertices_iff_original_unitary X x y)

end
end DaggerNativeOriginalFreeEC2UnitaryExistence
