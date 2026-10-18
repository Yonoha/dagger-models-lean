import NativeFixedDaggerIsomorphismPart
import ActualDaggerIsomorphismComponentFactor

/-! The EXACT original fixed-object factor through the all-isomorphism part.
All original objects, Hom simplices, both endpoint labels and dagger maps are retained.
This is the ordinary full-functor factor, not yet the whole enriched mapping-space ISO.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerNativeFixedDaggerIsomorphismPart
universe u
namespace DaggerNativeFixedDaggerPartFactor
noncomputable section

def factor {O : Type u} {H D : FixedDaggerCategory O} (F : H ⟶ D)
    (hH : HasActualComponentGroupoid (originalDagger H).toSimplicialCat) : H ⟶ part D where
  underlying :=
    { map := fun i j ↦
        (DaggerActualDaggerIsomorphismComponentFactor.factor (originalDaggerHom F) hH).map i j
      map_id := fun i ↦
        (DaggerActualDaggerIsomorphismComponentFactor.factor (originalDaggerHom F) hH).map_id i
      map_comp := fun i j k ↦
        (DaggerActualDaggerIsomorphismComponentFactor.factor
          (originalDaggerHom F) hH).map_comp i j k }
  map_dagger :=
    (DaggerActualDaggerIsomorphismComponentFactor.factor (originalDaggerHom F) hH).map_dagger

theorem factor_map_val {O : Type u} {H D : FixedDaggerCategory O} (F : H ⟶ D)
    (hH : HasActualComponentGroupoid (originalDagger H).toSimplicialCat)
    (i j : O) (q : SimplexCategoryᵒᵖ) (s : (H.underlying.enriched.Hom i j).obj q) :
    ((factor F hH).underlying.map i j |>.app q s).val =
      (F.underlying.map i j).app q s := rfl

theorem factor_comp_inclusion {O : Type u} {H D : FixedDaggerCategory O} (F : H ⟶ D)
    (hH : HasActualComponentGroupoid (originalDagger H).toSimplicialCat) :
    factor F hH ≫ inclusion D = F := by
  apply fixedDaggerHom_ext
  apply fixedHom_ext
  intro i j
  apply NatTrans.ext
  funext q s
  rfl

theorem inclusion_cancel {O : Type u} {H D : FixedDaggerCategory O} (F G : H ⟶ part D)
    (h : F ≫ inclusion D = G ≫ inclusion D) : F = G := by
  apply fixedDaggerHom_ext
  apply fixedHom_ext
  intro i j
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  exact congrFun (NatTrans.congr_app
    (congrArg (fun k : H ⟶ D ↦ k.underlying.map i j) h) q) s

theorem factor_unique {O : Type u} {H D : FixedDaggerCategory O} (F : H ⟶ D)
    (hH : HasActualComponentGroupoid (originalDagger H).toSimplicialCat)
    (G : H ⟶ part D) (hG : G ≫ inclusion D = F) : G = factor F hH :=
  inclusion_cancel G _ (hG.trans (factor_comp_inclusion F hH).symm)

theorem factor_natural {O : Type u} {H D E : FixedDaggerCategory O} (F : H ⟶ D) (G : D ⟶ E)
    (hH : HasActualComponentGroupoid (originalDagger H).toSimplicialCat) :
    factor (F ≫ G) hH = factor F hH ≫ map G := by
  apply inclusion_cancel
  rw [factor_comp_inclusion, Category.assoc, inclusion_natural,
    ← Category.assoc, factor_comp_inclusion]

def homEquiv {O : Type u} (H D : FixedDaggerCategory O)
    (hH : HasActualComponentGroupoid (originalDagger H).toSimplicialCat) :
    (H ⟶ part D) ≃ (H ⟶ D) where
  toFun F := F ≫ inclusion D
  invFun F := factor F hH
  left_inv F := (factor_unique (F ≫ inclusion D) hH F rfl).symm
  right_inv F := factor_comp_inclusion F hH

end
end DaggerNativeFixedDaggerPartFactor
