import NativeCoherentNerveIsomorphismPartKanFactor
import ActualLocallyKanGroupoidalCoherentNerve
import NativeKanSourceOriginalCoreFactor

/-! The ORIGINAL coherent nerve of the ALL-isomorphism part is its literal maximal Kan core. -/
set_option autoImplicit false
open CategoryTheory DaggerModels OrdinaryRigidification
open DaggerActualSimplicialIsomorphismComponentPart
open DaggerOriginalOrdinaryKanCoreSubcomplex
universe u
namespace DaggerActualCoherentNerveIsomorphismCore
noncomputable section

def forward (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    coherentNerve.obj (part C) ⟶ (ordinaryCoreCandidate (coherentNerve.obj C) : SSet.{u}) := by
  have := DaggerActualLocallyKanGroupoidalCoherentNerve.part_kan C hC
  exact DaggerNativeKanSourceOriginalCoreFactor.factor (coherentNerve.map (inclusion C))

def backward (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    (ordinaryCoreCandidate (coherentNerve.obj C) : SSet.{u}) ⟶ coherentNerve.obj (part C) := by
  have := DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory.coherentNerve_quasicategory
    C hC
  have := DaggerNativeKanSourceOriginalCoreFactor.native_quasi_core_kan (coherentNerve.obj C)
  exact DaggerNativeCoherentNerveIsomorphismPartKanFactor.factor C
    (ordinaryCoreCandidate (coherentNerve.obj C)).ι

theorem forward_comp (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    forward C hC ≫ (ordinaryCoreCandidate (coherentNerve.obj C)).ι =
      coherentNerve.map (inclusion C) := by
  have := DaggerActualLocallyKanGroupoidalCoherentNerve.part_kan C hC
  exact DaggerNativeKanSourceOriginalCoreFactor.factor_comp _

theorem backward_comp (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    backward C hC ≫ coherentNerve.map (inclusion C) =
      (ordinaryCoreCandidate (coherentNerve.obj C)).ι := by
  have := DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory.coherentNerve_quasicategory
    C hC
  have := DaggerNativeKanSourceOriginalCoreFactor.native_quasi_core_kan (coherentNerve.obj C)
  exact DaggerNativeCoherentNerveIsomorphismPartKanFactor.factor_comp_inclusion C _

def comparisonIso (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    coherentNerve.obj (part C) ≅ (ordinaryCoreCandidate (coherentNerve.obj C) : SSet.{u}) where
  hom := forward C hC
  inv := backward C hC
  hom_inv_id := by
    have := DaggerNativeCoherentNerveIsomorphismPartKanFactor.inclusion_mono C
    apply (cancel_mono (coherentNerve.map (inclusion C))).mp
    rw [Category.assoc, backward_comp, forward_comp, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (ordinaryCoreCandidate (coherentNerve.obj C)).ι).mp
    rw [Category.assoc, forward_comp, backward_comp, Category.id_comp]

theorem hom_comp_inclusion (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    (comparisonIso C hC).hom ≫ (ordinaryCoreCandidate (coherentNerve.obj C)).ι =
      coherentNerve.map (inclusion C) :=
  forward_comp C hC

theorem inv_comp_inclusion (C : SimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) :
    (comparisonIso C hC).inv ≫ coherentNerve.map (inclusion C) =
      (ordinaryCoreCandidate (coherentNerve.obj C)).ι :=
  backward_comp C hC

theorem nerve_inclusion_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    coherentNerve.map (DaggerActualSimplicialIsomorphismComponentMaps.map F) ≫
        coherentNerve.map (inclusion D) =
      coherentNerve.map (inclusion C) ≫ coherentNerve.map F := by
  rw [← coherentNerve.map_comp, ← coherentNerve.map_comp]
  exact congrArg (fun G : part C ⟶ D ↦ coherentNerve.map G)
    (DaggerActualSimplicialIsomorphismComponentMaps.inclusion_natural F)

theorem naturality {C D : SimplicialCat.{u, u}}
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y)) (F : C ⟶ D) :
    coherentNerve.map (DaggerActualSimplicialIsomorphismComponentMaps.map F) ≫
        (comparisonIso D hD).hom =
      (comparisonIso C hC).hom ≫ ordinaryCoreCandidateMap (coherentNerve.map F) := by
  apply (cancel_mono (ordinaryCoreCandidate (coherentNerve.obj D)).ι).mp
  calc
    (coherentNerve.map (DaggerActualSimplicialIsomorphismComponentMaps.map F) ≫
        (comparisonIso D hD).hom) ≫ (ordinaryCoreCandidate (coherentNerve.obj D)).ι =
      coherentNerve.map (DaggerActualSimplicialIsomorphismComponentMaps.map F) ≫
        coherentNerve.map (inclusion D) := by rw [Category.assoc, hom_comp_inclusion]
    _ = coherentNerve.map (inclusion C) ≫ coherentNerve.map F := nerve_inclusion_natural F
    _ = ((comparisonIso C hC).hom ≫ (ordinaryCoreCandidate (coherentNerve.obj C)).ι) ≫
        coherentNerve.map F := by rw [hom_comp_inclusion]
    _ = ((comparisonIso C hC).hom ≫ ordinaryCoreCandidateMap (coherentNerve.map F)) ≫
        (ordinaryCoreCandidate (coherentNerve.obj D)).ι := by
      rw [Category.assoc, Category.assoc, ordinaryCoreCandidateMap_comp_ι]

end
end DaggerActualCoherentNerveIsomorphismCore
