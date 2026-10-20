import NativeInternalHomCoproductComparison

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory
universe u
namespace DaggerNativeInternalHomCoproductTensorComparison
noncomputable section

/-- Compare the chosen limit product with the original cartesian monoidal tensor. -/
def productToTensorIso (X Y : SSet.{u}) : X ⨯ Y ≅ X ⊗ Y where
  hom := CartesianMonoidalCategory.lift prod.fst prod.snd
  inv := prod.lift (CartesianMonoidalCategory.fst X Y) (CartesianMonoidalCategory.snd X Y)
  hom_inv_id := by
    apply prod.hom_ext <;> simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp

def comparisonIso (A B Z : SSet.{u}) :
    (ihom (A ⨿ B)).obj Z ≅ (ihom A).obj Z ⊗ (ihom B).obj Z :=
  DaggerNativeInternalHomCoproductComparison.comparisonIso A B Z ≪≫
    productToTensorIso ((ihom A).obj Z) ((ihom B).obj Z)

theorem comparisonIso_hom_fst (A B Z : SSet.{u}) :
    (comparisonIso A B Z).hom ≫
        CartesianMonoidalCategory.fst ((ihom A).obj Z) ((ihom B).obj Z) =
      (MonoidalClosed.pre coprod.inl).app Z := by
  simp [comparisonIso, productToTensorIso,
    DaggerNativeInternalHomCoproductComparison.comparisonIso,
    DaggerNativeInternalHomCoproductComparison.comparisonHom]

theorem comparisonIso_hom_snd (A B Z : SSet.{u}) :
    (comparisonIso A B Z).hom ≫
        CartesianMonoidalCategory.snd ((ihom A).obj Z) ((ihom B).obj Z) =
      (MonoidalClosed.pre coprod.inr).app Z := by
  simp [comparisonIso, productToTensorIso,
    DaggerNativeInternalHomCoproductComparison.comparisonIso,
    DaggerNativeInternalHomCoproductComparison.comparisonHom]

theorem pre_naturality {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') (Z : SSet.{u}) :
    (MonoidalClosed.pre (coprod.map f g)).app Z ≫ (comparisonIso A B Z).hom =
      (comparisonIso A' B' Z).hom ≫
        ((MonoidalClosed.pre f).app Z ⊗ₘ (MonoidalClosed.pre g).app Z) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, comparisonIso_hom_fst,
      CartesianMonoidalCategory.tensorHom_fst]
    rw [← Category.assoc, comparisonIso_hom_fst]
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map,
      ← NatTrans.comp_app, ← MonoidalClosed.pre_map, coprod.inl_map]
  · simp only [Category.assoc, comparisonIso_hom_snd,
      CartesianMonoidalCategory.tensorHom_snd]
    rw [← Category.assoc, comparisonIso_hom_snd]
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map,
      ← NatTrans.comp_app, ← MonoidalClosed.pre_map, coprod.inr_map]

end
end DaggerNativeInternalHomCoproductTensorComparison
