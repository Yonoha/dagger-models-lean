import ChosenNecklaceDegreeGluing
import DaggerModels.SimplicialEnrichment

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode DaggerModels.SimplicialEnrichment

variable {T : NecklaceCode} (j : Fin (T.len + 1))
variable (D : DaggerModels.SimplicialCat.{u,u}) (d : Vertices.{u} T → D.Obj)

/-- Two actual enriched slice maps, including their complete local identity and composition laws. -/
structure SliceSSetMaps where
  left : ∀ (a b : Vertices.{u} T), a ≤ ULift.up j → b ≤ ULift.up j →
    (pathHom ⟨a⟩ ⟨b⟩ ⟶ (d a ⟶[SSet.{u}] d b))
  right : ∀ (a b : Vertices.{u} T), ULift.up j ≤ a → ULift.up j ≤ b →
    (pathHom ⟨a⟩ ⟨b⟩ ⟶ (d a ⟶[SSet.{u}] d b))
  left_id : ∀ (a : Vertices.{u} T) (ha : a ≤ ULift.up j),
    pathId ⟨a⟩ ≫ left a a ha ha = eId SSet (d a)
  right_id : ∀ (a : Vertices.{u} T) (ha : ULift.up j ≤ a),
    pathId ⟨a⟩ ≫ right a a ha ha = eId SSet (d a)
  left_comp : ∀ (a b c : Vertices.{u} T)
    (ha : a ≤ ULift.up j) (hb : b ≤ ULift.up j) (hc : c ≤ ULift.up j),
    pathComp ⟨a⟩ ⟨b⟩ ⟨c⟩ ≫ left a c ha hc =
      (left a b ha hb ⊗ₘ left b c hb hc) ≫ eComp SSet (d a) (d b) (d c)
  right_comp : ∀ (a b c : Vertices.{u} T)
    (ha : ULift.up j ≤ a) (hb : ULift.up j ≤ b) (hc : ULift.up j ≤ c),
    pathComp ⟨a⟩ ⟨b⟩ ⟨c⟩ ≫ right a c ha hc =
      (right a b ha hb ⊗ₘ right b c hb hc) ≫ eComp SSet (d a) (d b) (d c)

namespace SliceSSetMaps

variable {j D d} (S : SliceSSetMaps j D d)

/-- The original degree categories, with all the original local Hom maps. -/
def degree (q : SimplexCategoryᵒᵖ) : SliceChainMaps q j (At D.Obj q) d where
  left a b ha hb := (S.left a b ha hb).app q
  right a b ha hb := (S.right a b ha hb).app q
  left_id a ha := congrFun (NatTrans.congr_app (S.left_id a ha) q) PUnit.unit
  right_id a ha := congrFun (NatTrans.congr_app (S.right_id a ha) q) PUnit.unit
  left_comp a b c ha hb hc F G :=
    congrFun (NatTrans.congr_app (S.left_comp a b c ha hb hc) q) (F, G)
  right_comp a b c ha hb hc F G :=
    congrFun (NatTrans.congr_app (S.right_comp a b c ha hb hc) q) (F, G)

variable (hj : j ∈ T.joints)

theorem target_comp_natural (a b c : D.Obj) {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (F : (a ⟶[SSet.{u}] b).obj q) (G : (b ⟶[SSet.{u}] c).obj q) :
    (a ⟶[SSet.{u}] c).map α ((eComp SSet a b c).app q (F, G)) =
      (eComp SSet a b c).app r ((a ⟶[SSet.{u}] b).map α F,
        (b ⟶[SSet.{u}] c).map α G) :=
  (DaggerModels.SimplicialEnrichment.map D.Obj α).map_comp F G

/-- Full Hom natural transformation; each crossing is the original two-slice composition. -/
def hom (a b : Vertices.{u} T) : pathHom ⟨a⟩ ⟨b⟩ ⟶ (d a ⟶[SSet.{u}] d b) where
  app q := glueChain q j hj (S.degree q)
  naturality q r α := by
    funext F
    change glueChain r j hj (S.degree r) ((pathHom ⟨a⟩ ⟨b⟩).map α F) =
      (d a ⟶[SSet.{u}] d b).map α (glueChain q j hj (S.degree q) F)
    by_cases ha : ULift.up j ≤ a
    · simp only [glueChain, dif_pos ha]
      exact congrFun ((S.right a b ha (ha.trans (chain_le q F))).naturality α) F
    · by_cases hb : ULift.up j ≤ b
      · simp only [glueChain, dif_neg ha, dif_pos hb]
        change (eComp SSet (d a) (d (ULift.up j)) (d b)).app r
          ((S.left a (ULift.up j) (le_of_lt (lt_of_not_ge ha)) le_rfl).app r
            (splitChainLeft q j hj (le_of_lt (lt_of_not_ge ha)) hb F |>
              (pathHom ⟨a⟩ ⟨ULift.up j⟩).map α),
           (S.right (ULift.up j) b le_rfl hb).app r
            ((pathHom ⟨ULift.up j⟩ ⟨b⟩).map α
              (splitChainRight q j hj (le_of_lt (lt_of_not_ge ha)) hb F))) =
          (d a ⟶[SSet.{u}] d b).map α
            ((eComp SSet (d a) (d (ULift.up j)) (d b)).app q
              ((S.left a (ULift.up j) (le_of_lt (lt_of_not_ge ha)) le_rfl).app q
                (splitChainLeft q j hj (le_of_lt (lt_of_not_ge ha)) hb F),
               (S.right (ULift.up j) b le_rfl hb).app q
                (splitChainRight q j hj (le_of_lt (lt_of_not_ge ha)) hb F)))
        rw [target_comp_natural]
        exact congrArg₂ (fun l k ↦ (eComp SSet (d a) (d (ULift.up j)) (d b)).app r (l, k))
          (congrFun ((S.left a (ULift.up j) (le_of_lt (lt_of_not_ge ha)) le_rfl).naturality α)
            (splitChainLeft q j hj (le_of_lt (lt_of_not_ge ha)) hb F))
          (congrFun ((S.right (ULift.up j) b le_rfl hb).naturality α)
            (splitChainRight q j hj (le_of_lt (lt_of_not_ge ha)) hb F))
      · simp only [glueChain, dif_neg ha, dif_neg hb]
        exact congrFun ((S.left a b (le_of_lt (lt_of_not_ge ha))
          (le_of_lt (lt_of_not_ge hb))).naturality α) F

/-- The complete enriched descent across the joint, with the supplied object labels. -/
def desc : NC.{u} T ⟶ D where
  obj a := d a.as
  map a b := S.hom hj a.as b.as
  map_id a := by
    apply NatTrans.ext
    funext q v
    cases v
    exact glueChain_id q j hj (S.degree q) a.as
  map_comp a b c := by
    apply NatTrans.ext
    funext q v
    rcases v with ⟨F,G⟩
    exact glueChain_comp q j hj (S.degree q) F G

end SliceSSetMaps

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
