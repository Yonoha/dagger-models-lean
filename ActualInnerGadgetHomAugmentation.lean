import ActualInnerGadgetHomWeights
import NativeSimplicialReplacementReindex

/-! Augment the literal endpoint-Hom weights by the whole original gadget maps into X. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerActualInnerIteratedGadgetData DaggerChosenRigidificationNecklace
open DaggerActualInnerGadgetHomWeights DaggerNativeSimplicialReplacement
open DaggerSSetGluing
universe u
namespace DaggerActualInnerGadgetHomAugmentation
noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

/-- Keep each actual gadget's original code and the complete original map of codes. -/
def forget : DaggerActualInnerIteratedGadgetData.Over X a b ⥤ Code where
  obj P := P.code
  map f := f.hom

def diagram : DaggerActualInnerIteratedGadgetData.Over X a b ⥤ SSet.{u} :=
  forget X a b ⋙ weights

/-- The apex is the unchanged original rigidification Hom of X, with its original vertex labels. -/
abbrev originalHom := RV X a ⟶[SSet.{u}] RV X b

theorem original_source (P : DaggerActualInnerIteratedGadgetData.Over X a b) :
    (rigidification.map P.map).obj (source P.code) = RV X a :=
  (RigidificationVertices.vertexEquiv_naturality P.map (alpha P.code)).trans
    (congrArg (RV X) P.first)

theorem original_target (P : DaggerActualInnerIteratedGadgetData.Over X a b) :
    (rigidification.map P.map).obj (target P.code) = RV X b :=
  (RigidificationVertices.vertexEquiv_naturality P.map (omega P.code)).trans
    (congrArg (RV X) P.last)

/-- Apply the full original C(P.map), including both exact endpoint transports. -/
def leg (P : DaggerActualInnerIteratedGadgetData.Over X a b) :
    (diagram X a b).obj P ⟶ originalHom X a b :=
  castMap (rigidification.map P.map) (source P.code) (target P.code)
    (RV X a) (RV X b) (original_source X a b P) (original_target X a b P)

/-- The original enriched Hom maps assemble with every entire original gadget morphism. -/
def augmentation : diagram X a b ⟶
    (Functor.const (DaggerActualInnerIteratedGadgetData.Over X a b)).obj (originalHom X a b) where
  app := leg X a b
  naturality {P Q} f := by
    change castMap (rigidification.map f.hom.map)
        (source P.code) (target P.code) (source Q.code) (target Q.code)
        (source_map f.hom) (target_map f.hom) ≫
      castMap (rigidification.map Q.map) (source Q.code) (target Q.code)
        (RV X a) (RV X b) (original_source X a b Q) (original_target X a b Q) =
      leg X a b P ≫ 𝟙 _
    rw [Category.comp_id, ← castMap_comp]
    exact castMap_congr
      ((rigidification.map_comp f.hom.map Q.map).symm.trans
        (congrArg rigidification.map f.w))
      (source P.code) (target P.code) (RV X a) (RV X b) _ _ _ _

/-- The full original replacement augmentation retains the original parameter simplex. -/
def toOriginalHom :
    DaggerBisimplicialDiagonal.diag (replacement (diagram X a b)) ⟶ originalHom X a b :=
  diagonalAugmentation (diagram X a b) (augmentation X a b)

/-- All actual weights are contractible by the existing original endpoint-Hom theorem. -/
theorem diagram_point_GW (P : DaggerActualInnerIteratedGadgetData.Over X a b) :
    GW (DaggerOriginalProductGadget.pointMap ((diagram X a b).obj P)) :=
  weights_point_GW P.code

/-- The exact weighted replacement projects weakly to the original whole gadget nerve. -/
theorem projection_GW : GW (diagonalProjection (diagram X a b)) :=
  diagonalProjection_GW (diagram X a b) (diagram_point_GW X a b)

end
end DaggerActualInnerGadgetHomAugmentation
