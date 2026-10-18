import OriginalCotensorEvaluationRowMaps
import NativeBisimplicialDiagonalColimits

/-! The entire original endpoint coproduct bar is retained as an actual bisimplicial arrow. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite DaggerModels
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryDiagonalNerve DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalSimplicialCategoryOverDiagram DaggerOriginalCotensorEvaluationRowMaps
open DaggerOriginalNerveRowChainData DaggerNativeBisimplicialHorizontalMapping
open DaggerNativeBisimplicialDiagonal DaggerNativeBisimplicialDiagonalColimits
universe u
namespace DaggerOriginalWholeBarBisimplicial
noncomputable section

def componentProjection (C : SimplicialCat.{u, u}) (z : C.Obj) : barRows C z ⟶ baseRows C :=
  (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map
    (Functor.whiskerRight (overCategoryProjection C z) nerveFunctor)

def wholeRows (C : SimplicialCat.{u, u}) : BiSSet.{u} := ∐ (barRows C)
def wholeProjection (C : SimplicialCat.{u, u}) : wholeRows C ⟶ baseRows C :=
  Limits.Sigma.desc (componentProjection C)

def componentDiagonalIso (C : SimplicialCat.{u, u}) (z : C.Obj) :
    diagonalFunctor.obj (barRows C z) ≅ barComponent C z :=
  diagonalFlipIso (barBisimplicial C z)

def baseDiagonalIso (C : SimplicialCat.{u, u}) :
    diagonalFunctor.obj (baseRows C) ≅ diagonalNerveFunctor.obj C :=
  diagonalFlipIso (bisimplicialNerveFunctor.obj C)

def wholeDiagonalIso (C : SimplicialCat.{u, u}) :
    diagonalFunctor.obj (wholeRows C) ≅ bar C :=
  (diagonalSigmaIso (barRows C)).symm ≪≫
    asIso (Limits.Sigma.map (fun z ↦ (componentDiagonalIso C z).hom))

theorem componentProjection_diagonal (C : SimplicialCat.{u, u}) (z : C.Obj) :
    diagonalFunctor.map (componentProjection C z) ≫ (baseDiagonalIso C).hom =
      (componentDiagonalIso C z).hom ≫ barComponentProjection C z := by
  apply NatTrans.ext
  rfl

theorem wholeDiagonalIso_inclusion (C : SimplicialCat.{u, u}) (z : C.Obj) :
    diagonalFunctor.map (Limits.Sigma.ι (barRows C) z) ≫ (wholeDiagonalIso C).hom =
      (componentDiagonalIso C z).hom ≫ barInclusion C z := by
  have hh := ι_comp_sigmaComparison diagonalFunctor (barRows C) z
  rw [← hh]
  simp only [wholeDiagonalIso, diagonalSigmaIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc, Limits.Sigma.ι_map, barInclusion]

theorem wholeProjection_diagonal (C : SimplicialCat.{u, u}) :
    diagonalFunctor.map (wholeProjection C) ≫ (baseDiagonalIso C).hom =
      (wholeDiagonalIso C).hom ≫ barProjection C := by
  apply (cancel_epi (diagonalSigmaIso (barRows C)).hom).mp
  apply Limits.Sigma.hom_ext
  intro z
  change Limits.Sigma.ι (fun z ↦ diagonalFunctor.obj (barRows C z)) z ≫
      sigmaComparison diagonalFunctor (barRows C) ≫
        diagonalFunctor.map (wholeProjection C) ≫ (baseDiagonalIso C).hom = _
  simp only [diagonalSigmaIso, asIso_hom]
  simp only [← Category.assoc]
  rw [ι_comp_sigmaComparison, ← diagonalFunctor.map_comp,
    wholeProjection, Limits.Sigma.ι_desc]
  rw [wholeDiagonalIso_inclusion,
    Category.assoc, barInclusion_projection]
  exact componentProjection_diagonal C z

def wholeRowsMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : wholeRows C ⟶ wholeRows D :=
  Limits.Sigma.desc (fun z ↦ barRowsMap F z ≫ Limits.Sigma.ι (barRows D) (F.obj z))

theorem componentProjection_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (z : C.Obj) :
    barRowsMap F z ≫ componentProjection D (F.obj z) =
      componentProjection C z ≫ baseRowsMap F := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  rfl

theorem wholeProjection_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    wholeRowsMap F ≫ wholeProjection D = wholeProjection C ≫ baseRowsMap F := by
  apply Limits.Sigma.hom_ext
  intro z
  have ha : Limits.Sigma.ι (barRows C) z ≫ wholeRowsMap F =
      barRowsMap F z ≫ Limits.Sigma.ι (barRows D) (F.obj z) := Limits.Sigma.ι_desc _ _
  have hb : Limits.Sigma.ι (barRows C) z ≫ wholeProjection C = componentProjection C z :=
    Limits.Sigma.ι_desc _ _
  have hc : Limits.Sigma.ι (barRows D) (F.obj z) ≫ wholeProjection D =
      componentProjection D (F.obj z) := Limits.Sigma.ι_desc _ _
  change (Limits.Sigma.ι (barRows C) z ≫ wholeRowsMap F) ≫ wholeProjection D =
    (Limits.Sigma.ι (barRows C) z ≫ wholeProjection C) ≫ baseRowsMap F
  rw [ha, Category.assoc, hc, hb]
  exact componentProjection_natural F z

theorem componentMap_diagonal {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (z : C.Obj) :
    diagonalFunctor.map (barRowsMap F z) ≫ (componentDiagonalIso D (F.obj z)).hom =
      (componentDiagonalIso C z).hom ≫ barComponentMap F z := by
  apply NatTrans.ext
  rfl

theorem baseMap_diagonal {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    diagonalFunctor.map (baseRowsMap F) ≫ (baseDiagonalIso D).hom =
      (baseDiagonalIso C).hom ≫ diagonalNerveFunctor.map F := by
  apply NatTrans.ext
  rfl

theorem wholeMap_diagonal {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    diagonalFunctor.map (wholeRowsMap F) ≫ (wholeDiagonalIso D).hom =
      (wholeDiagonalIso C).hom ≫ barMap F := by
  apply (cancel_epi (diagonalSigmaIso (barRows C)).hom).mp
  apply Limits.Sigma.hom_ext
  intro z
  change Limits.Sigma.ι (fun z ↦ diagonalFunctor.obj (barRows C z)) z ≫
      sigmaComparison diagonalFunctor (barRows C) ≫ diagonalFunctor.map (wholeRowsMap F) ≫
        (wholeDiagonalIso D).hom = _
  simp only [diagonalSigmaIso, asIso_hom]
  simp only [← Category.assoc]
  rw [ι_comp_sigmaComparison, ← diagonalFunctor.map_comp,
    wholeRowsMap, Limits.Sigma.ι_desc, diagonalFunctor.map_comp]
  rw [Category.assoc, wholeDiagonalIso_inclusion, ← Category.assoc, componentMap_diagonal]
  rw [wholeDiagonalIso_inclusion]
  simp only [Category.assoc]
  rw [barInclusion_map]


end
end DaggerOriginalWholeBarBisimplicial
