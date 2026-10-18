import NativeDaggerRestrictionInclusion
import OriginalFixedObjectGroupoidCompletionAdjunction
import ActualDaggerCoreEndpointRestriction

/-! Full original object restriction preserves strict groupoids even with repeated labels.
Complete the WHOLE original core rigidification before selecting the SAME two endpoints.
-/
set_option autoImplicit false
open CategoryTheory Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerNativeDaggerObjectRestriction DaggerActualDaggerOrdinaryCore
universe u
namespace DaggerNativeStrictDaggerObjectRestriction
noncomputable section

theorem restriction_strict {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj)
    (hD : IsStrictGroupoid D.toSimplicialCat) :
    IsStrictGroupoid (original O (restriction D θ).underlying) := by
  intro n x y f
  let F := degreeFunctor (DaggerNativeDaggerRestrictionInclusion.inclusion D θ).toEnrichedFunctor n
  let hF : F.FullyFaithful :=
    { preimage := fun g ↦ g
      map_preimage := fun g ↦ rfl
      preimage_map := fun g ↦ rfl }
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  have : IsIso (F.map f) := hD n _ _ _
  exact isIso_of_reflects_iso f F

def strictRestriction {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj)
    (hD : IsStrictGroupoid D.toSimplicialCat) : FixedStrictDaggerGroupoids O :=
  ⟨restriction D θ, restriction_strict D θ hD⟩

def strictCoreTarget (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet _⦋0⦌) :
    FixedStrictDaggerGroupoids TwoObjectDaggerGraph.Vertex.{u} :=
  strictRestriction (daggerCompletion (DaggerRigidification.obj (coreDagger X)))
    (DaggerActualDaggerCoreEndpointRestriction.labels X x y)
    (completion_isStrictGroupoid (DaggerRigidification.obj (coreDagger X)).toSimplicialCat)

theorem strictCoreTarget_obj (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet _⦋0⦌) :
    (strictCoreTarget X x y).obj = DaggerActualDaggerCoreEndpointRestriction.target X x y := rfl

end
end DaggerNativeStrictDaggerObjectRestriction
