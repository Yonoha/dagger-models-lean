import TopCatModelCategory.ModelCategorySSet

/-! Actual horizontal mapping and matching objects for native bisimplicial sets. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBisimplicialHorizontalMapping
noncomputable section

abbrev BiSSet := SimplexCategoryᵒᵖ ⥤ SSet.{u}

def horizontalMapping (K : SSet.{u}) (X : BiSSet.{u}) : SSet.{u} :=
  X.flip ⋙ coyoneda.obj (op K)

def horizontalPre {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u}) :
    horizontalMapping L X ⟶ horizontalMapping K X where
  app _ a := i ≫ a
  naturality v w α := by
    funext a
    change i ≫ (a ≫ X.flip.map α) = (i ≫ a) ≫ X.flip.map α
    exact (Category.assoc _ _ _).symm

def horizontalMap (K : SSet.{u}) {X Y : BiSSet.{u}} (f : X ⟶ Y) :
    horizontalMapping K X ⟶ horizontalMapping K Y :=
  Functor.whiskerRight
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f)
    (coyoneda.obj (op K))

theorem horizontalPre_id (K : SSet.{u}) (X : BiSSet.{u}) :
    horizontalPre (𝟙 K) X = 𝟙 _ := by
  ext v a
  exact Category.id_comp a

theorem horizontalPre_comp {K L M : SSet.{u}} (i : K ⟶ L) (j : L ⟶ M)
    (X : BiSSet.{u}) : horizontalPre (i ≫ j) X = horizontalPre j X ≫ horizontalPre i X := by
  ext v a
  exact Category.assoc _ _ _

theorem horizontalMap_id (K : SSet.{u}) (X : BiSSet.{u}) :
    horizontalMap K (𝟙 X) = 𝟙 _ := by
  ext v a
  exact Category.comp_id a

theorem horizontalMap_comp (K : SSet.{u}) {X Y Z : BiSSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    horizontalMap K (f ≫ g) = horizontalMap K f ≫ horizontalMap K g := by
  ext v a
  change a ≫
      (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f).app v ≫
        ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map g).app v) = _
  exact (Category.assoc _ _ _).symm

theorem horizontalPre_natural {K L : SSet.{u}} (i : K ⟶ L)
    {X Y : BiSSet.{u}} (f : X ⟶ Y) :
    horizontalPre i X ≫ horizontalMap K f = horizontalMap L f ≫ horizontalPre i Y := by
  ext v a
  change (i ≫ a) ≫
      ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f).app v = _
  exact Category.assoc _ _ _

def horizontalSimplexIso (X : BiSSet.{u}) (m : ℕ) :
    horizontalMapping (Δ[m] : SSet.{u}) X ≅ X.obj (op ⦋m⦌) :=
  NatIso.ofComponents (fun v ↦ SSet.yonedaEquiv.toIso) (by
    intro v w α
    funext a
    exact SSet.yonedaEquiv_comp a (X.flip.map α))

theorem horizontalSimplexIso_hom_app (X : BiSSet.{u}) (m : ℕ)
    (v : SimplexCategoryᵒᵖ) (a : (Δ[m] : SSet.{u}) ⟶ X.flip.obj v) :
    (horizontalSimplexIso X m).hom.app v a = SSet.yonedaEquiv a := rfl

theorem horizontalSimplexIso_natural {X Y : BiSSet.{u}} (f : X ⟶ Y) (m : ℕ) :
    horizontalMap (Δ[m] : SSet.{u}) f ≫ (horizontalSimplexIso Y m).hom =
      (horizontalSimplexIso X m).hom ≫ f.app (op ⦋m⦌) := by
  ext v a
  exact SSet.yonedaEquiv_comp a
    (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f).app v)

def relativeRestriction {K L : SSet.{u}} (i : K ⟶ L)
    {X Y : BiSSet.{u}} (f : X ⟶ Y) : horizontalMapping L X ⟶
      pullback (horizontalMap K f) (horizontalPre i Y) :=
  pullback.lift (horizontalPre i X) (horizontalMap L f) (horizontalPre_natural i f)

theorem relativeRestriction_fst {K L : SSet.{u}} (i : K ⟶ L)
    {X Y : BiSSet.{u}} (f : X ⟶ Y) : relativeRestriction i f ≫
      pullback.fst (horizontalMap K f) (horizontalPre i Y) = horizontalPre i X := by
  simp only [relativeRestriction, pullback.lift_fst]

theorem relativeRestriction_snd {K L : SSet.{u}} (i : K ⟶ L)
    {X Y : BiSSet.{u}} (f : X ⟶ Y) : relativeRestriction i f ≫
      pullback.snd (horizontalMap K f) (horizontalPre i Y) = horizontalMap L f := by
  simp only [relativeRestriction, pullback.lift_snd]

def matching (X : BiSSet.{u}) (m : ℕ) : SSet.{u} :=
  horizontalMapping (SSet.boundary m : SSet.{u}) X

def hornMatching (X : BiSSet.{u}) (m : ℕ) (k : Fin (m + 1)) : SSet.{u} :=
  horizontalMapping (SSet.horn m k : SSet.{u}) X

def ReedyFibration {X Y : BiSSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ m : ℕ, Fibration (relativeRestriction (SSet.boundary m).ι f)

end
end DaggerNativeBisimplicialHorizontalMapping
