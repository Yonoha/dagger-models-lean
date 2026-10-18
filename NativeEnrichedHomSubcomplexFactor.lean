import NativeEnrichedHomSubcomplexRestriction

/-! Factor original enriched functors through Hom subcomplexes with the same values. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerNativeEnrichedHomSubcomplexRestriction
universe u
namespace DaggerNativeEnrichedHomSubcomplexFactor
noncomputable section

variable {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
variable (A : ∀ x y : D.Obj, (D.enriched.Hom x y).Subcomplex)
variable (hi : ∀ (x : D.Obj) (q : SimplexCategoryᵒᵖ) (s : (𝟙_ SSet.{u}).obj q),
  (D.enriched.id x).app q s ∈ (A x x).obj q)
variable (hc : ∀ (x y z : D.Obj) (q : SimplexCategoryᵒᵖ)
  (s : (A x y : SSet.{u}).obj q) (t : (A y z : SSet.{u}).obj q),
  (D.enriched.comp x y z).app q (s.val, t.val) ∈ (A x z).obj q)
variable (hf : ∀ (x y : C.Obj) (q : SimplexCategoryᵒᵖ) (s : (C.enriched.Hom x y).obj q),
  (F.map x y).app q s ∈ (A (F.obj x) (F.obj y)).obj q)

def factor : C ⟶ restricted D A hi hc where
  obj := F.obj
  map x y :=
    { app := fun q s ↦ ⟨(F.map x y).app q s, hf x y q s⟩
      naturality := by
        intro q r f
        funext s
        apply Subtype.ext
        exact congrFun ((F.map x y).naturality f) s }
  map_id x := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (F.map_id x) q) s
  map_comp x y z := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact congrFun (NatTrans.congr_app (F.map_comp x y z) q) s

theorem factor_comp_inclusion : factor F A hi hc hf ≫ inclusion D A hi hc = F := by
  letI := C.enriched
  letI := D.enriched
  apply EnrichedFunctor.ext SSet
    (F := factor F A hi hc hf ≫ inclusion D A hi hc) (G := F) (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

theorem factor_map_val (x y : C.Obj) (q : SimplexCategoryᵒᵖ)
    (s : (C.enriched.Hom x y).obj q) :
    ((factor F A hi hc hf).map x y |>.app q s).val = (F.map x y).app q s :=
  rfl

end
end DaggerNativeEnrichedHomSubcomplexFactor
