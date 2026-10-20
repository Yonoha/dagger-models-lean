import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

set_option autoImplicit false
set_option maxHeartbeats 0
open CategoryTheory Limits

universe w v u
namespace DaggerTransfinitePushoutData
noncomputable section

variable {V : Type u} [Category.{v} V] {J : Type w}
  [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {C B C' : V} {i : C ⟶ B} (h : TransfiniteCompositionOfShape J i)

def sourceMap (j : J) : C ⟶ h.F.obj j := h.isoBot.inv ≫ h.F.map (homOfLE bot_le)

def sourceNat : (Functor.const J).obj C ⟶ h.F where
  app := sourceMap h
  naturality j k t := by
    change (𝟙 C) ≫ sourceMap h k = sourceMap h j ≫ h.F.map t
    rw [Category.id_comp]
    dsimp [sourceMap]
    rw [Category.assoc, ← Functor.map_comp]
    rfl

@[reassoc (attr := simp)]
theorem sourceMap_naturality {j k : J} (t : j ⟶ k) :
    sourceMap h j ≫ h.F.map t = sourceMap h k := by
  have ht := ((sourceNat h).naturality t).symm
  change sourceMap h j ≫ h.F.map t = (𝟙 C) ≫ sourceMap h k at ht
  simpa only [Category.id_comp] using ht

@[simp] theorem sourceMap_bot : sourceMap h ⊥ = h.isoBot.inv := by
  simp [sourceMap]

def underDiagram : J ⥤ Under C := Under.lift h.F (sourceNat h)

variable (F : C ⟶ C') [HasPushoutsAlong F]

def diagram : J ⥤ V := underDiagram h ⋙ Under.pushout F ⋙ Under.forget C'

@[simp] theorem diagram_obj (j : J) :
    (diagram h F).obj j = pushout (sourceMap h j) F := rfl

def eta : h.F ⟶ diagram h F where
  app j := pushout.inl (sourceMap h j) F
  naturality j k t := by
    dsimp [diagram, underDiagram, Under.lift, Under.pushout, sourceNat]
    simp

def sourceLeg : (Functor.const J).obj C' ⟶ diagram h F where
  app j := pushout.inr (sourceMap h j) F
  naturality j k t := by
    dsimp [diagram, underDiagram, Under.lift, Under.pushout, sourceNat]
    simp

@[reassoc (attr := simp)]
theorem eta_naturality {j k : J} (t : j ⟶ k) :
    (eta h F).app j ≫ (diagram h F).map t = h.F.map t ≫ (eta h F).app k :=
  ((eta h F).naturality t).symm

@[reassoc (attr := simp)]
theorem sourceLeg_naturality {j k : J} (t : j ⟶ k) :
    (sourceLeg h F).app j ≫ (diagram h F).map t = (sourceLeg h F).app k := by
  have ht := ((sourceLeg h F).naturality t).symm
  change (sourceLeg h F).app j ≫ (diagram h F).map t =
    (𝟙 C') ≫ (sourceLeg h F).app k at ht
  simpa only [Category.id_comp] using ht

theorem stageSquare (j : J) :
    IsPushout (sourceMap h j) F ((eta h F).app j) ((sourceLeg h F).app j) :=
  IsPushout.of_hasPushout _ _

@[reassoc (attr := simp)]
theorem stage_condition (j : J) :
    sourceMap h j ≫ (eta h F).app j = F ≫ (sourceLeg h F).app j :=
  (stageSquare h F j).w

theorem transitionSquare {j k : J} (t : j ⟶ k) :
    IsPushout ((eta h F).app j) (h.F.map t)
      ((diagram h F).map t) ((eta h F).app k) := by
  have outer : IsPushout (sourceMap h j ≫ h.F.map t) F
      ((eta h F).app k) ((sourceLeg h F).app j ≫ (diagram h F).map t) := by
    rw [sourceMap_naturality, sourceLeg_naturality]
    exact stageSquare h F k
  exact (outer.of_left ((eta h F).naturality t) (stageSquare h F j)).flip

instance sourceMap_bot_isIso : IsIso (sourceMap h ⊥) := by
  rw [sourceMap_bot]
  infer_instance

instance sourceLeg_bot_isIso : IsIso ((sourceLeg h F).app ⊥) :=
  (stageSquare h F ⊥).isIso_inr_of_isIso

def botIso : (diagram h F).obj ⊥ ≅ C' := (asIso ((sourceLeg h F).app ⊥)).symm

@[simp] theorem botIso_inv : (botIso h F).inv = (sourceLeg h F).app ⊥ := rfl

@[reassoc (attr := simp)]
theorem botIso_hom_inv : (botIso h F).hom ≫ (botIso h F).inv = 𝟙 _ :=
  (botIso h F).hom_inv_id

@[reassoc (attr := simp)]
theorem botIso_inv_hom : (botIso h F).inv ≫ (botIso h F).hom = 𝟙 _ :=
  (botIso h F).inv_hom_id

@[reassoc (attr := simp)]
theorem bot_source_leg : h.isoBot.inv ≫ (eta h F).app ⊥ = F ≫ (botIso h F).inv := by
  simpa only [sourceMap_bot, botIso_inv] using stage_condition h F ⊥

@[reassoc (attr := simp)]
theorem bot_eta : (eta h F).app ⊥ ≫ (botIso h F).hom = h.isoBot.hom ≫ F := by
  calc
    (eta h F).app ⊥ ≫ (botIso h F).hom =
        h.isoBot.hom ≫ (h.isoBot.inv ≫ (eta h F).app ⊥) ≫ (botIso h F).hom := by
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = h.isoBot.hom ≫ (F ≫ (botIso h F).inv) ≫ (botIso h F).hom := by
      rw [bot_source_leg]
    _ = h.isoBot.hom ≫ F := by
      simp only [Category.assoc, botIso_inv_hom, Category.comp_id]

end
end DaggerTransfinitePushoutData
