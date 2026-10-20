import NativeEnrichedHomSubcomplexFactor

/-! Inherit the original dagger on Hom subcomplexes stable under that same dagger. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerNativeEnrichedHomSubcomplexRestriction
universe u
namespace DaggerNativeDaggerEnrichedHomRestriction
noncomputable section

variable (D : DaggerSimplicialCat.{u, u})
variable (A : ∀ x y : D.Obj, (D.enriched.Hom x y).Subcomplex)
variable (hi : ∀ (x : D.Obj) (q : SimplexCategoryᵒᵖ) (s : (𝟙_ SSet.{u}).obj q),
  (D.enriched.id x).app q s ∈ (A x x).obj q)
variable (hc : ∀ (x y z : D.Obj) (q : SimplexCategoryᵒᵖ)
  (s : (A x y : SSet.{u}).obj q) (t : (A y z : SSet.{u}).obj q),
  (D.enriched.comp x y z).app q (s.val, t.val) ∈ (A x z).obj q)
variable (hd : ∀ (x y : D.Obj) (q : SimplexCategoryᵒᵖ)
  (s : (A x y : SSet.{u}).obj q), (D.daggerStructure.dagger x y).app q s.val ∈ (A y x).obj q)

def daggerMap (x y : D.Obj) : (A x y : SSet.{u}) ⟶ (A y x : SSet.{u}) where
  app q s := ⟨(D.daggerStructure.dagger x y).app q s.val, hd x y q s⟩
  naturality := by
    intro q r f
    funext s
    apply Subtype.ext
    exact congrFun ((D.daggerStructure.dagger x y).naturality f) s.val

def daggerStructure :
    @DaggerSimplicialStructure D.Obj (enriched D.toSimplicialCat A hi hc) := by
  letI := enriched D.toSimplicialCat A hi hc
  exact
    { dagger := daggerMap D A hd
      dagger_involutive x y := by
        apply NatTrans.ext
        funext q s
        apply Subtype.ext
        exact congrFun (NatTrans.congr_app (D.daggerStructure.dagger_involutive x y) q) s.val
      dagger_id x := by
        apply NatTrans.ext
        funext q s
        apply Subtype.ext
        exact congrFun (NatTrans.congr_app (D.daggerStructure.dagger_id x) q) s
      dagger_comp x y z := by
        apply NatTrans.ext
        funext q s
        apply Subtype.ext
        exact congrFun (NatTrans.congr_app (D.daggerStructure.dagger_comp x y z) q)
          (s.1.val, s.2.val) }

def restricted : DaggerSimplicialCat.{u, u} where
  toSimplicialCat := DaggerNativeEnrichedHomSubcomplexRestriction.restricted
    D.toSimplicialCat A hi hc
  daggerStructure := daggerStructure D A hi hc hd

def inclusion : restricted D A hi hc hd ⟶ D where
  toEnrichedFunctor := DaggerNativeEnrichedHomSubcomplexRestriction.inclusion
    D.toSimplicialCat A hi hc
  map_dagger x y := by
    apply NatTrans.ext
    funext q s
    rfl

theorem inclusion_map (x y : D.Obj) : (inclusion D A hi hc hd).map x y = (A x y).ι :=
  rfl

theorem dagger_val (x y : D.Obj) (q : SimplexCategoryᵒᵖ)
    (s : (A x y : SSet.{u}).obj q) :
    ((daggerMap D A hd x y).app q s).val = (D.daggerStructure.dagger x y).app q s.val :=
  rfl

end
end DaggerNativeDaggerEnrichedHomRestriction
