import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Functor.Currying

/-! SOURCE-ONLY CANDIDATE. No declaration in this file has been compiled in this batch. -/

open CategoryTheory

universe u

namespace DaggerBisimplicialDiagonal

/-- Existing uncurrying, precomposed by the existing index diagonal. -/
def diagonalFunctor : SimplicialObject SSet.{u} ⥤ SSet.{u} :=
  (Functor.uncurry :
    (SimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Type u) ⥤
      (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ Type u)) ⋙
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (Type u)).obj
      (Functor.diag SimplexCategoryᵒᵖ)

abbrev diag (B : SimplicialObject SSet.{u}) : SSet.{u} := diagonalFunctor.obj B

abbrev diagMap {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') :
    diag B ⟶ diag B' := diagonalFunctor.map eta

@[simp] theorem diag_obj (B : SimplicialObject SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    (diag B).obj q = (B.obj q).obj q := rfl

/-- The original accepted outer-first order is the actual uncurry order. -/
@[simp] theorem diag_map (B : SimplicialObject SSet.{u})
    {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (diag B).map beta = (B.map beta).app q ≫ (B.obj r).map beta := rfl

theorem diag_map_other_order (B : SimplicialObject SSet.{u})
    {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (diag B).map beta = (B.obj q).map beta ≫ (B.map beta).app r := by
  exact ((B.map beta).naturality beta).symm

@[simp] theorem diagMap_app {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (q : SimplexCategoryᵒᵖ) : (diagMap eta).app q = (eta.app q).app q := rfl

/-- Whole laws come from the existing composed functors, rather than new raw data. -/
theorem diag_map_id (B : SimplicialObject SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    (diag B).map (𝟙 q) = 𝟙 ((diag B).obj q) := (diag B).map_id q

theorem diag_map_comp (B : SimplicialObject SSet.{u})
    {q r s : SimplexCategoryᵒᵖ} (beta : q ⟶ r) (gamma : r ⟶ s) :
    (diag B).map (beta ≫ gamma) = (diag B).map beta ≫ (diag B).map gamma :=
  (diag B).map_comp beta gamma

@[simp] theorem diagMap_id (B : SimplicialObject SSet.{u}) :
    diagMap (𝟙 B) = 𝟙 (diag B) := diagonalFunctor.map_id B

@[simp] theorem diagMap_comp {B B' B'' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (theta : B' ⟶ B'') :
    diagMap (eta ≫ theta) = diagMap eta ≫ diagMap theta :=
  diagonalFunctor.map_comp eta theta

theorem diagMap_operator {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (diag B).map beta ≫ (diagMap eta).app r =
      (diagMap eta).app q ≫ (diag B').map beta :=
  (diagMap eta).naturality beta

/-- Flip has the same diagonal objects and reverses the two operator orders. -/
def diagFlipIso (B : SimplicialObject SSet.{u}) : diag B.flip ≅ diag B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro q r beta
    change ((B.obj q).map beta ≫ (B.map beta).app r) ≫ 𝟙 _ =
      𝟙 _ ≫ ((B.map beta).app q ≫ (B.obj r).map beta)
    simpa only [Category.comp_id, Category.id_comp] using (B.map beta).naturality beta)

@[simp] theorem diagFlipIso_hom_app (B : SimplicialObject SSet.{u})
    (q : SimplexCategoryᵒᵖ) : (diagFlipIso B).hom.app q = 𝟙 ((B.obj q).obj q) := rfl

@[simp] theorem diagFlipIso_inv_app (B : SimplicialObject SSet.{u})
    (q : SimplexCategoryᵒᵖ) : (diagFlipIso B).inv.app q = 𝟙 ((B.obj q).obj q) := rfl

theorem diagFlipIso_hom_inv (B : SimplicialObject SSet.{u}) :
    (diagFlipIso B).hom ≫ (diagFlipIso B).inv = 𝟙 (diag B.flip) :=
  (diagFlipIso B).hom_inv_id

theorem diagFlipIso_inv_hom (B : SimplicialObject SSet.{u}) :
    (diagFlipIso B).inv ≫ (diagFlipIso B).hom = 𝟙 (diag B) :=
  (diagFlipIso B).inv_hom_id

theorem diagFlipIso_naturality {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') :
    diagMap ((flipFunctor _ _ _).map eta) ≫ (diagFlipIso B').hom =
      (diagFlipIso B).hom ≫ diagMap eta := by
  ext q : 1
  change (eta.app q).app q ≫ 𝟙 _ = 𝟙 _ ≫ (eta.app q).app q
  simp only [Category.comp_id, Category.id_comp]

theorem diagFlipIso_inv_naturality {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') :
    diagMap eta ≫ (diagFlipIso B').inv =
      (diagFlipIso B).inv ≫ diagMap ((flipFunctor _ _ _).map eta) := by
  ext q : 1
  change (eta.app q).app q ≫ 𝟙 _ = 𝟙 _ ≫ (eta.app q).app q
  simp only [Category.comp_id, Category.id_comp]

/-- The full eta-naturality is packaged as a natural isomorphism of functors. -/
def diagonalFlipIso :
    flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u) ⋙ diagonalFunctor ≅
      diagonalFunctor :=
  NatIso.ofComponents diagFlipIso (by
    intro B B' eta
    exact diagFlipIso_naturality eta)

theorem diag_flip_flip (B : SimplicialObject SSet.{u}) : diag B.flip.flip = diag B :=
  congrArg diag (Functor.flip_flip B)

end DaggerBisimplicialDiagonal
