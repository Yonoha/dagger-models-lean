import NativeDaggerEnrichedHomRestriction

/-! Factor original dagger maps through a stable Hom subcomplex with original values. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerNativeDaggerEnrichedHomRestriction
universe u
namespace DaggerNativeDaggerEnrichedHomFactor
noncomputable section

variable {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
variable (A : ∀ x y : D.Obj, (D.enriched.Hom x y).Subcomplex)
variable (hi : ∀ (x : D.Obj) (q : SimplexCategoryᵒᵖ) (s : (𝟙_ SSet.{u}).obj q),
  (D.enriched.id x).app q s ∈ (A x x).obj q)
variable (hc : ∀ (x y z : D.Obj) (q : SimplexCategoryᵒᵖ)
  (s : (A x y : SSet.{u}).obj q) (t : (A y z : SSet.{u}).obj q),
  (D.enriched.comp x y z).app q (s.val, t.val) ∈ (A x z).obj q)
variable (hd : ∀ (x y : D.Obj) (q : SimplexCategoryᵒᵖ)
  (s : (A x y : SSet.{u}).obj q), (D.daggerStructure.dagger x y).app q s.val ∈ (A y x).obj q)
variable (hf : ∀ (x y : C.Obj) (q : SimplexCategoryᵒᵖ) (s : (C.enriched.Hom x y).obj q),
  (F.map x y).app q s ∈ (A (F.obj x) (F.obj y)).obj q)

def factor : C ⟶ restricted D A hi hc hd where
  toEnrichedFunctor := DaggerNativeEnrichedHomSubcomplexFactor.factor
    F.toEnrichedFunctor A hi hc hf
  map_dagger x y := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (F.map_dagger x y) q) s

theorem factor_comp_inclusion_underlying :
    (factor F A hi hc hd hf ≫ inclusion D A hi hc hd).toEnrichedFunctor =
      F.toEnrichedFunctor :=
  DaggerNativeEnrichedHomSubcomplexFactor.factor_comp_inclusion _ _ _ _ _

theorem factor_comp_inclusion : factor F A hi hc hd hf ≫ inclusion D A hi hc hd = F := by
  apply DaggerSimplicialCat.Hom.ext
  exact factor_comp_inclusion_underlying F A hi hc hd hf

theorem factor_map_val (x y : C.Obj) (q : SimplexCategoryᵒᵖ)
    (s : (C.enriched.Hom x y).obj q) :
    ((factor F A hi hc hd hf).map x y |>.app q s).val = (F.map x y).app q s :=
  rfl

end
end DaggerNativeDaggerEnrichedHomFactor
