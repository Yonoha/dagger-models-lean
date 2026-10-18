import ActualMappingCoreVertexCharacterization
import NativePrefixMappingSubcomplexRestriction

/-! The SAME original core mapping fibre is the full equivalence-vertex part, with both anchors. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerActualQuasicategoryMappingFibres DaggerActualMappingCoreVertexCharacterization
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalFullVertexSubcomplex
universe u
namespace DaggerActualCoreMappingFullVertexIso
noncomputable section

def coreVertex (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌) :=
  ⟨a, vertex_mem_ordinaryCoreCandidate X a⟩

def coreRestrictionIso (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    leftMapping (ordinaryCoreCandidate X : SSet.{u}) (coreVertex X a) (coreVertex X b) ≅
      (corePart X a b : SSet.{u}) :=
  DaggerNativePrefixMappingSubcomplexRestriction.restrictionIso X (ordinaryCoreCandidate X)
    ⦋0⦌ (coreVertex X a) (coreVertex X b)

def comparisonIso (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    leftMapping (ordinaryCoreCandidate X : SSet.{u}) (coreVertex X a) (coreVertex X b) ≅
      (fullVertexSubcomplex (leftMapping X a b) (equivalenceVertices X a b) : SSet.{u}) :=
  coreRestrictionIso X a b ≪≫ SSet.Subcomplex.isoOfEq (corePart_eq_fullVertex X a b)

theorem hom_comp_inclusion (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    (comparisonIso X a b).hom ≫
        (fullVertexSubcomplex (leftMapping X a b) (equivalenceVertices X a b)).ι =
      map (ordinaryCoreCandidate X).ι ⦋0⦌ (coreVertex X a) (coreVertex X b) := by
  change ((coreRestrictionIso X a b).hom ≫
    (SSet.Subcomplex.isoOfEq (corePart_eq_fullVertex X a b)).hom) ≫ _ = _
  rw [Category.assoc, SSet.Subcomplex.isoOfEq_hom_ι]
  exact DaggerNativePrefixMappingSubcomplexRestriction.restrictionIso_hom_comp X
    (ordinaryCoreCandidate X) ⦋0⦌ (coreVertex X a) (coreVertex X b)

theorem inv_comp_inclusion (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    (comparisonIso X a b).inv ≫
        map (ordinaryCoreCandidate X).ι ⦋0⦌ (coreVertex X a) (coreVertex X b) =
      (fullVertexSubcomplex (leftMapping X a b) (equivalenceVertices X a b)).ι := by
  apply (cancel_epi (comparisonIso X a b).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, hom_comp_inclusion]

theorem hom_raw_value (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ)
    (s : (leftMapping (ordinaryCoreCandidate X : SSet.{u})
      (coreVertex X a) (coreVertex X b)).obj q) :
    ((comparisonIso X a b).hom.app q s).val.val.val = s.val.val.val :=
  congrArg (fun t : (leftMapping X a b).obj q ↦ t.val.val)
    (congrFun (NatTrans.congr_app (hom_comp_inclusion X a b) q) s)

theorem inv_raw_value (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ)
    (s : (fullVertexSubcomplex (leftMapping X a b) (equivalenceVertices X a b) :
      SSet.{u}).obj q) :
    ((comparisonIso X a b).inv.app q s).val.val.val = s.val.val.val :=
  congrArg (fun t : (leftMapping X a b).obj q ↦ t.val.val)
    (congrFun (NatTrans.congr_app (inv_comp_inclusion X a b) q) s)

theorem coreMapping_kan (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    (leftMapping (ordinaryCoreCandidate X : SSet.{u})
      (coreVertex X a) (coreVertex X b)).KanComplex := by
  have := DaggerNativeKanSourceOriginalCoreFactor.native_quasi_core_kan X
  exact leftMapping_kan (ordinaryCoreCandidate X : SSet.{u}) (coreVertex X a) (coreVertex X b)

theorem selectedMapping_kan (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    (fullVertexSubcomplex (leftMapping X a b) (equivalenceVertices X a b) :
      SSet.{u}).KanComplex := by
  have := coreMapping_kan X a b
  exact DaggerNativeKanSimplicialOpposite.kan_of_iso (comparisonIso X a b)

end
end DaggerActualCoreMappingFullVertexIso
