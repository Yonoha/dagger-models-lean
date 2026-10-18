import NativeInternalHomOppositeComparison

/-!
# The actual internal Hom of a binary coproduct

The comparison is the product of the two original precomposition maps.
Its inverse uses native currying and the coproduct comparison for tensoring.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory
universe u
namespace DaggerNativeInternalHomCoproductComparison
noncomputable section

local instance nativeBraiding : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

local instance tensorRightPreservesBinaryCoproducts (U : SSet.{u}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight U) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight U)

def comparisonHom (A B Z : SSet.{u}) :
    (ihom (A ⨿ B)).obj Z ⟶ (ihom A).obj Z ⨯ (ihom B).obj Z :=
  prod.lift ((MonoidalClosed.pre coprod.inl).app Z)
    ((MonoidalClosed.pre coprod.inr).app Z)

def comparisonInv (A B Z : SSet.{u}) :
    (ihom A).obj Z ⨯ (ihom B).obj Z ⟶ (ihom (A ⨿ B)).obj Z :=
  MonoidalClosed.curry
    (inv (coprodComparison (tensorRight ((ihom A).obj Z ⨯ (ihom B).obj Z)) A B) ≫
      coprod.desc (MonoidalClosed.uncurry prod.fst) (MonoidalClosed.uncurry prod.snd))

theorem comparisonInv_pre_inl (A B Z : SSet.{u}) :
    comparisonInv A B Z ≫ (MonoidalClosed.pre coprod.inl).app Z = prod.fst := by
  rw [comparisonInv, MonoidalClosed.curry_pre_app]
  change MonoidalClosed.curry
    ((tensorRight _).map coprod.inl ≫ inv (coprodComparison (tensorRight _) A B) ≫ _) = _
  rw [map_inl_inv_coprodComparison_assoc, coprod.inl_desc, MonoidalClosed.curry_uncurry]

theorem comparisonInv_pre_inr (A B Z : SSet.{u}) :
    comparisonInv A B Z ≫ (MonoidalClosed.pre coprod.inr).app Z = prod.snd := by
  rw [comparisonInv, MonoidalClosed.curry_pre_app]
  change MonoidalClosed.curry
    ((tensorRight _).map coprod.inr ≫ inv (coprodComparison (tensorRight _) A B) ≫ _) = _
  rw [map_inr_inv_coprodComparison_assoc, coprod.inr_desc, MonoidalClosed.curry_uncurry]

/-- A map into the original internal Hom is determined by both original restrictions. -/
theorem pre_hom_ext {A B Z U : SSet.{u}} (k l : U ⟶ (ihom (A ⨿ B)).obj Z)
    (hl : k ≫ (MonoidalClosed.pre coprod.inl).app Z =
      l ≫ (MonoidalClosed.pre coprod.inl).app Z)
    (hr : k ≫ (MonoidalClosed.pre coprod.inr).app Z =
      l ≫ (MonoidalClosed.pre coprod.inr).app Z) : k = l := by
  apply MonoidalClosed.uncurry_injective
  apply (cancel_epi (coprodComparison (tensorRight U) A B)).1
  apply coprod.hom_ext
  · rw [coprodComparison_inl_assoc, coprodComparison_inl_assoc]
    simpa only [MonoidalClosed.uncurry_pre_app] using congrArg MonoidalClosed.uncurry hl
  · rw [coprodComparison_inr_assoc, coprodComparison_inr_assoc]
    simpa only [MonoidalClosed.uncurry_pre_app] using congrArg MonoidalClosed.uncurry hr

def comparisonIso (A B Z : SSet.{u}) :
    (ihom (A ⨿ B)).obj Z ≅ (ihom A).obj Z ⨯ (ihom B).obj Z where
  hom := comparisonHom A B Z
  inv := comparisonInv A B Z
  hom_inv_id := by
    apply pre_hom_ext
    · simp only [Category.assoc, comparisonInv_pre_inl, comparisonHom, prod.lift_fst,
        Category.id_comp]
    · simp only [Category.assoc, comparisonInv_pre_inr, comparisonHom, prod.lift_snd,
        Category.id_comp]
  inv_hom_id := by
    apply prod.hom_ext
    · simp only [comparisonHom, prod.lift_fst, Category.assoc, comparisonInv_pre_inl,
        Category.id_comp]
    · simp only [comparisonHom, prod.lift_snd, Category.assoc, comparisonInv_pre_inr,
        Category.id_comp]

theorem pre_naturality {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') (Z : SSet.{u}) :
    (MonoidalClosed.pre (coprod.map f g)).app Z ≫ (comparisonIso A B Z).hom =
      (comparisonIso A' B' Z).hom ≫
        prod.map ((MonoidalClosed.pre f).app Z) ((MonoidalClosed.pre g).app Z) := by
  apply prod.hom_ext
  · simp only [comparisonIso, comparisonHom, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc]
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map,
      ← NatTrans.comp_app, ← MonoidalClosed.pre_map, coprod.inl_map]
  · simp only [comparisonIso, comparisonHom, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc]
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map,
      ← NatTrans.comp_app, ← MonoidalClosed.pre_map, coprod.inr_map]

end
end DaggerNativeInternalHomCoproductComparison
