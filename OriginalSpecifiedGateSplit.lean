import OriginalWedgeCutFlags

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a v b : X.obj (op ⦋0⦌)}

/-- A left cut at a supplied source vertex, retaining its specified target endpoint. -/
def specifiedLeftOver (P : NecklacesOver X a b) (k : Fin (P.code.len + 1))
    (hv : cutMiddleVertex P k = v) : NecklacesOver X a v where
  code := (cutLeftOver P k).code
  map := (cutLeftOver P k).map
  first := (cutLeftOver P k).first
  last := (cutLeftOver P k).last.trans hv

/-- A right cut at that same source vertex, retaining the same specified target endpoint. -/
def specifiedRightOver (P : NecklacesOver X a b) (k : Fin (P.code.len + 1))
    (hv : cutMiddleVertex P k = v) : NecklacesOver X v b where
  code := (cutRightOver P k).code
  map := (cutRightOver P k).map
  first := (cutRightOver P k).first.trans hv
  last := (cutRightOver P k).last

/-- The supplied-joint split is defined on any original necklace, without a Mono premise. -/
def specifiedSplit (P : NecklacesOver X a b) (k : Fin (P.code.len + 1))
    (hk : k ∈ P.code.joints) (hv : cutMiddleVertex P k = v) :
    flagSSet P.code ⟶ flagHom X a v ⊗ flagHom X v b :=
  (cutFlagIso P.code k hk).hom ≫
    (flagLeg X a v (specifiedLeftOver P k hv) ⊗ₘ
      flagLeg X v b (specifiedRightOver P k hv))

variable {P Q : NecklacesOver X a b} (f : P ⟶ Q)
  (k : Fin (P.code.len + 1)) (l : Fin (Q.code.len + 1))
  (h : orderMap f.hom.map k = l)
  (hv : cutMiddleVertex P k = v) (hw : cutMiddleVertex Q l = v)

def specifiedLeftMap : specifiedLeftOver P k hv ⟶ specifiedLeftOver Q l hw where
  hom := cutLeftHom f.hom k l h
  w := cutLeftOver_naturality f k l h

def specifiedRightMap : specifiedRightOver P k hv ⟶ specifiedRightOver Q l hw where
  hom := cutRightHom f.hom k l h
  w := cutRightOver_naturality f k l h

include h in
/-- Naturality holds even when the original source necklace is not monomorphic. -/
theorem specifiedSplit_naturality (hk : k ∈ P.code.joints) (hl : l ∈ Q.code.joints) :
    flagMap f.hom ≫ specifiedSplit Q l hl hw = specifiedSplit P k hk hv := by
  apply NatTrans.ext
  funext q F
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d
  have he := cutFlagOver_map (n := d) f k l h hk hl F
  change (Quot.mk (flagRelation X a v (op ⦋d⦌))
      ⟨specifiedLeftOver Q l hw,
        ((cutFlagIso Q.code l hl).hom.app (op ⦋d⦌) (NecklaceCode.Flag.map f.hom F)).1⟩,
    Quot.mk (flagRelation X v b (op ⦋d⦌))
      ⟨specifiedRightOver Q l hw,
        ((cutFlagIso Q.code l hl).hom.app (op ⦋d⦌) (NecklaceCode.Flag.map f.hom F)).2⟩) = _
  rw [he]
  apply Prod.ext
  · exact (Quot.sound ⟨specifiedLeftMap f k l h hv hw, rfl⟩).symm
  · exact (Quot.sound ⟨specifiedRightMap f k l h hv hw, rfl⟩).symm

variable (L : NecklacesOver X a v) (R : NecklacesOver X v b)

/-- The original wedge joint maps to the originally specified common endpoint. -/
theorem wedgeCut_middle :
    cutMiddleVertex (NecklacesOver.wedge L R) (wedgeCutJoint L.code R.code) = v := by
  have he := (wedgeLeftIntervalOver L.code R.code).last
  change (wedgeιLeft L.code R.code).app _ L.code.last = _ at he
  change (NecklacesOver.wedge L R).map.app _ _ = v
  exact (congrArg ((NecklacesOver.wedge L R).map.app _) he.symm).trans
    ((congrFun (NatTrans.congr_app (NecklacesOver.wedge_left L R) _) L.code.last).trans L.last)

/-- The left wedge factor maps to the actual left cut over the same original target. -/
def specifiedWedgeLeftMap : L ⟶ specifiedLeftOver (NecklacesOver.wedge L R)
    (wedgeCutJoint L.code R.code) (wedgeCut_middle L R) where
  hom := wedgeLeftCutHom L.code R.code
  w := by
    change (wedgeLeftCutHom L.code R.code).map ≫
      (cutLeftι _ _ ≫ (NecklacesOver.wedge L R).map) = L.map
    rw [← Category.assoc, wedgeLeftCutHom_fac, NecklacesOver.wedge_left]

/-- The right wedge factor maps to the actual right cut over the same original target. -/
def specifiedWedgeRightMap : R ⟶ specifiedRightOver (NecklacesOver.wedge L R)
    (wedgeCutJoint L.code R.code) (wedgeCut_middle L R) where
  hom := wedgeRightCutHom L.code R.code
  w := by
    change (wedgeRightCutHom L.code R.code).map ≫
      (cutRightι _ _ ≫ (NecklacesOver.wedge L R).map) = R.map
    rw [← Category.assoc, wedgeRightCutHom_fac, NecklacesOver.wedge_right]

/-- Cutting the original wedge flag recovers the original two Hom classes, in every degree. -/
theorem specifiedSplit_wedge {d : ℕ} (F : Flag.{u} L.code d) (G : Flag.{u} R.code d) :
    (specifiedSplit (NecklacesOver.wedge L R) (wedgeCutJoint L.code R.code)
      (wedgeCutJoint_mem L.code R.code) (wedgeCut_middle L R)).app (op ⦋d⦌)
        (NecklaceCode.Flag.wedge F G) =
      (Quot.mk (flagRelation X a v (op ⦋d⦌)) ⟨L, F⟩,
        Quot.mk (flagRelation X v b (op ⦋d⦌)) ⟨R, G⟩) := by
  change (Quot.mk (flagRelation X a v (op ⦋d⦌))
      ⟨specifiedLeftOver _ _ (wedgeCut_middle L R),
        ((cutFlagIso _ _ (wedgeCutJoint_mem L.code R.code)).hom.app (op ⦋d⦌)
          (NecklaceCode.Flag.wedge F G)).1⟩,
    Quot.mk (flagRelation X v b (op ⦋d⦌))
      ⟨specifiedRightOver _ _ (wedgeCut_middle L R),
        ((cutFlagIso _ _ (wedgeCutJoint_mem L.code R.code)).hom.app (op ⦋d⦌)
          (NecklaceCode.Flag.wedge F G)).2⟩) = _
  rw [cutFlagIso_wedge]
  apply Prod.ext
  · exact (Quot.sound ⟨specifiedWedgeLeftMap L R, rfl⟩).symm
  · exact (Quot.sound ⟨specifiedWedgeRightMap L R, rfl⟩).symm

end

end DaggerOriginalProductGadget
