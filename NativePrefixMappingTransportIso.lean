import ActualQuasicategoryMappingFibres

/-! Full native prefix maps with BOTH prescribed endpoint equalities, and exact iso transport. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerActualQuasicategoryMappingFibres
universe u
namespace DaggerNativePrefixMappingTransportIso
noncomputable section

def mapTo {X Y : SSet.{u}} (f : X ⟶ Y) (k : SimplexCategory)
    (σ : X.obj (op k)) (b : X.obj (op ⦋0⦌))
    (τ : Y.obj (op k)) (c : Y.obj (op ⦋0⦌))
    (hσ : f.app (op k) σ = τ) (hb : f.app (op ⦋0⦌) b = c) :
    prefixMapping X k σ b ⟶ prefixMapping Y k τ c := by
  subst τ
  subst c
  exact map f k σ b

theorem mapTo_raw {X Y : SSet.{u}} (f : X ⟶ Y) (k : SimplexCategory)
    (σ : X.obj (op k)) (b : X.obj (op ⦋0⦌))
    (τ : Y.obj (op k)) (c : Y.obj (op ⦋0⦌))
    (hσ : f.app (op k) σ = τ) (hb : f.app (op ⦋0⦌) b = c)
    (q : SimplexCategoryᵒᵖ) (s : (prefixMapping X k σ b).obj q) :
    ((mapTo f k σ b τ c hσ hb).app q s).val.val =
      f.app (op ((ordinalJoinLeft k).obj q.unop)) s.val.val := by
  subst τ
  subst c
  rfl

def mappingIso {X Y : SSet.{u}} (e : X ≅ Y) (k : SimplexCategory)
    (σ : X.obj (op k)) (b : X.obj (op ⦋0⦌))
    (τ : Y.obj (op k)) (c : Y.obj (op ⦋0⦌))
    (hσ : e.hom.app (op k) σ = τ) (hb : e.hom.app (op ⦋0⦌) b = c) :
    prefixMapping X k σ b ≅ prefixMapping Y k τ c where
  hom := mapTo e.hom k σ b τ c hσ hb
  inv := mapTo e.inv k τ c σ b
    (by
      rw [← hσ]
      exact congrFun (NatTrans.congr_app e.hom_inv_id (op k)) σ)
    (by
      rw [← hb]
      exact congrFun (NatTrans.congr_app e.hom_inv_id (op ⦋0⦌)) b)
  hom_inv_id := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    apply Subtype.ext
    change ((mapTo e.inv k τ c σ b _ _).app q
      ((mapTo e.hom k σ b τ c hσ hb).app q s)).val.val = s.val.val
    rw [mapTo_raw, mapTo_raw]
    exact congrFun (NatTrans.congr_app e.hom_inv_id
      (op ((ordinalJoinLeft k).obj q.unop))) s.val.val
  inv_hom_id := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    apply Subtype.ext
    change ((mapTo e.hom k σ b τ c hσ hb).app q
      ((mapTo e.inv k τ c σ b _ _).app q s)).val.val = s.val.val
    rw [mapTo_raw, mapTo_raw]
    exact congrFun (NatTrans.congr_app e.inv_hom_id
      (op ((ordinalJoinLeft k).obj q.unop))) s.val.val

end
end DaggerNativePrefixMappingTransportIso
