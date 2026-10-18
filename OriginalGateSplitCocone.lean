import OriginalGateJointChoice
import ChosenFlagEnrichment

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a v b : X.obj (op ⦋0⦌)}

/-- The left cuts form a functor into the original monomorphic-necklace category. -/
def gateLeftFunctor : MonicGateNecklaces a b {v} ⥤ MonicGateNecklaces a v ∅ where
  obj P := ⟨gateLeftOver P, gateLeftOver_mono P, Set.empty_subset _⟩
  map f := ObjectProperty.homMk (gateLeftMap f)
  map_id P := by
    apply ObjectProperty.hom_ext
    apply NecklacesOver.Hom.ext
    exact cutLeftHom_id P.obj.code (gateJoint P)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply NecklacesOver.Hom.ext
    exact cutLeftHom_comp f.hom.hom g.hom.hom _ _ _
      (gateJoint_naturality f) (gateJoint_naturality g)

/-- The right cuts form a functor with the same specified middle endpoint. -/
def gateRightFunctor : MonicGateNecklaces a b {v} ⥤ MonicGateNecklaces v b ∅ where
  obj P := ⟨gateRightOver P, gateRightOver_mono P, Set.empty_subset _⟩
  map f := ObjectProperty.homMk (gateRightMap f)
  map_id P := by
    apply ObjectProperty.hom_ext
    apply NecklacesOver.Hom.ext
    exact cutRightHom_id P.obj.code (gateJoint P)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply NecklacesOver.Hom.ext
    exact cutRightHom_comp f.hom.hom g.hom.hom _ _ _
      (gateJoint_naturality f) (gateJoint_naturality g)

/-- Cut the original flag and take its two original Hom classes. -/
def gateSplitLeg (P : MonicGateNecklaces a b {v}) :
    flagSSet P.obj.code ⟶ flagHom X a v ⊗ flagHom X v b :=
  (cutFlagIso P.obj.code (gateJoint P) (gateJoint_mem P)).hom ≫
    (flagLeg X a v (gateLeftOver P) ⊗ₘ flagLeg X v b (gateRightOver P))

/-- The cut flags descend along every original arrow of the restricted full subcategory. -/
theorem gateSplitLeg_naturality {P Q : MonicGateNecklaces a b {v}} (f : P ⟶ Q) :
    flagMap f.hom.hom ≫ gateSplitLeg Q = gateSplitLeg P := by
  apply NatTrans.ext
  funext q F
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d
  have h := cutFlagOver_map (n := d) f.hom (gateJoint P) (gateJoint Q) (gateJoint_naturality f)
    (gateJoint_mem P) (gateJoint_mem Q) F
  change (Quot.mk (flagRelation X a v (op ⦋d⦌)) ⟨gateLeftOver Q,
      ((cutFlagIso Q.obj.code (gateJoint Q) (gateJoint_mem Q)).hom.app (op ⦋d⦌)
        (NecklaceCode.Flag.map f.hom.hom F)).1⟩,
    Quot.mk (flagRelation X v b (op ⦋d⦌)) ⟨gateRightOver Q,
      ((cutFlagIso Q.obj.code (gateJoint Q) (gateJoint_mem Q)).hom.app (op ⦋d⦌)
        (NecklaceCode.Flag.map f.hom.hom F)).2⟩) = _
  rw [h]
  apply Prod.ext
  · exact (Quot.sound ⟨gateLeftMap f, rfl⟩).symm
  · exact (Quot.sound ⟨gateRightMap f, rfl⟩).symm

variable (a v b)

/-- The actual Hom-product cocone on all monomorphic necklaces through the given joint. -/
def gateSplitCocone : Cocone (monicGateFlagDiagram a b {v}) where
  pt := flagHom X a v ⊗ flagHom X v b
  ι := { app := gateSplitLeg, naturality _ _ f := gateSplitLeg_naturality f }

/-- Full colimit descent makes the split independent of the chosen necklace representative. -/
def gateSplit : monicGateHom a b {v} ⟶ flagHom X a v ⊗ flagHom X v b :=
  (monicGateIsColimit a b {v}).desc (gateSplitCocone a v b)

theorem gateSplit_leg (P : MonicGateNecklaces a b {v}) :
    monicGateLeg a b {v} P ≫ gateSplit a v b = gateSplitLeg P := rfl

variable {a v b}

/-- Recombining the two cuts retains a literal original over-X arrow to the supplied necklace. -/
def gateWedgeOver (P : MonicGateNecklaces a b {v}) :
    NecklacesOver.wedge (gateLeftOver P) (gateRightOver P) ⟶ P.obj where
  hom := cutWedgeHom P.obj.code (gateJoint P)
  w := (cutWedgeOver P.obj (gateJoint P)).w

/-- On each original representative, split followed by the original composition is unchanged. -/
theorem gateSplitLeg_comp (P : MonicGateNecklaces a b {v}) :
    gateSplitLeg P ≫ flagComposition X a v b = flagLeg X a b P.obj := by
  ext q F
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d
  exact Quot.sound ⟨gateWedgeOver P,
    (cutWedge_split_flag P.obj.code (gateJoint P) (gateJoint_mem P) F).symm⟩

/-- The descended split recovers the literal original Hom class under the original composition. -/
theorem gateSplit_comp :
    gateSplit a v b ≫ flagComposition X a v b = monicGateToHom a b {v} := by
  ext q x
  induction x using Quot.ind with | _ p
  exact congrFun (NatTrans.congr_app (gateSplitLeg_comp p.1) q) p.2

end

end DaggerOriginalProductGadget
