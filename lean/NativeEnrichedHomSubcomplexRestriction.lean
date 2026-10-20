import ActualConstantSimplicialCategory

/-! Restrict original simplicial Homs to subcomplexes closed under identity and composition. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
universe u
namespace DaggerNativeEnrichedHomSubcomplexRestriction
noncomputable section

variable (C : SimplicialCat.{u, u})
variable (A : ∀ x y : C.Obj, (C.enriched.Hom x y).Subcomplex)
variable (hi : ∀ (x : C.Obj) (q : SimplexCategoryᵒᵖ) (s : (𝟙_ SSet.{u}).obj q),
  (C.enriched.id x).app q s ∈ (A x x).obj q)
variable (hc : ∀ (x y z : C.Obj) (q : SimplexCategoryᵒᵖ)
  (s : (A x y : SSet.{u}).obj q) (t : (A y z : SSet.{u}).obj q),
  (C.enriched.comp x y z).app q (s.val, t.val) ∈ (A x z).obj q)

def idMap (x : C.Obj) : 𝟙_ SSet.{u} ⟶ (A x x : SSet.{u}) where
  app q s := ⟨(C.enriched.id x).app q s, hi x q s⟩
  naturality _ _ f := by
    funext s
    apply Subtype.ext
    exact congrFun ((C.enriched.id x).naturality f) s

def compMap (x y z : C.Obj) :
    (A x y : SSet.{u}) ⊗ (A y z : SSet.{u}) ⟶ (A x z : SSet.{u}) where
  app q s := ⟨(C.enriched.comp x y z).app q (s.1.val, s.2.val), hc x y z q s.1 s.2⟩
  naturality _ _ f := by
    funext s
    apply Subtype.ext
    exact congrFun ((C.enriched.comp x y z).naturality f) (s.1.val, s.2.val)

def enriched : EnrichedCategory SSet.{u} C.Obj where
  Hom x y := (A x y : SSet.{u})
  id := idMap C A hi
  comp := compMap C A hc
  id_comp x y := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (C.enriched.id_comp x y) q) s.val
  comp_id x y := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (C.enriched.comp_id x y) q) s.val
  assoc w x y z := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (C.enriched.assoc w x y z) q)
      (s.1.val, (s.2.1.val, s.2.2.val))

def restricted : SimplicialCat.{u, u} :=
  ⟨C.Obj, enriched C A hi hc⟩

def inclusion : restricted C A hi hc ⟶ C where
  obj := id
  map x y := (A x y).ι
  map_id _ := rfl
  map_comp _ _ _ := rfl

theorem inclusion_map (x y : C.Obj) : (inclusion C A hi hc).map x y = (A x y).ι :=
  rfl

end
end DaggerNativeEnrichedHomSubcomplexRestriction
