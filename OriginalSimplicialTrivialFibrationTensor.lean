import OriginalFixedObjectAmbientDaggerModel

/-!
# Trivial fibrations of the exact native simplicial tensor product

Use the native Cartesian tensor product's limiting cone and the native binary
product. Model-category trivial fibrations are stable under base change and
composition, so the comparison transports the actual two-coordinate map.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalSimplicialTrivialFibrationTensor
noncomputable section

/-- The actual simplicial tensor product is the native categorical binary product. -/
def tensorProductIso (A B : SSet.{u}) : A ⊗ B ≅ A ⨯ B :=
  (CartesianMonoidalCategory.tensorProductIsBinaryProduct A B).conePointUniqueUpToIso
    (limit.isLimit (pair A B))

/-- The full product comparison retains the actual first Hom coordinate. -/
theorem tensorProductIso_fst (A B : SSet.{u}) :
    (tensorProductIso A B).hom ≫ prod.fst = CartesianMonoidalCategory.fst A B :=
  (CartesianMonoidalCategory.tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair A B)) ⟨.left⟩

/-- The full product comparison retains the actual second Hom coordinate. -/
theorem tensorProductIso_snd (A B : SSet.{u}) :
    (tensorProductIso A B).hom ≫ prod.snd = CartesianMonoidalCategory.snd A B :=
  (CartesianMonoidalCategory.tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair A B)) ⟨.right⟩

/-- The entire native tensor map agrees with the product map under these exact isomorphisms. -/
theorem tensorProductIso_natural {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D) :
    (f ⊗ₘ g) ≫ (tensorProductIso B D).hom =
      (tensorProductIso A C).hom ≫ prod.map f g := by
  apply prod.hom_ext
  · simp only [Category.assoc, tensorProductIso_fst,
      CartesianMonoidalCategory.tensorHom_fst, prod.map_fst]
    rw [← Category.assoc, tensorProductIso_fst]
  · simp only [Category.assoc, tensorProductIso_snd,
      CartesianMonoidalCategory.tensorHom_snd, prod.map_snd]
    rw [← Category.assoc, tensorProductIso_snd]

/-- Base change and composition give trivial fibrancy of the full native binary product map. -/
theorem prodMap_trivialFibration {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : trivialFibrations SSet.{u} f) (hg : trivialFibrations SSet.{u} g) :
    trivialFibrations SSet.{u} (prod.map f g) := by
  let P := trivialFibrations SSet.{u}
  have h₁ : P (prod.map f (𝟙 C)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id f C) hf
  have hs : P (prod.map g (𝟙 B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_prod_fst_with_id g B) hg
  have h₂ : P (prod.map (𝟙 B) g) := by
    have h := P.comp_mem _ _
      (P.comp_mem _ _ (P.of_isIso (prod.braiding B C).hom) hs)
      (P.of_isIso (prod.braiding D B).hom)
    convert h using 1
    apply prod.hom_ext <;> simp
  have h := P.comp_mem _ _ h₁ h₂
  convert h using 1
  apply prod.hom_ext <;> simp

/-- The actual tensor of two original simplicial trivial fibrations is a trivial fibration. -/
theorem tensorHom_trivialFibration {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : trivialFibrations SSet.{u} f) (hg : trivialFibrations SSet.{u} g) :
    trivialFibrations SSet.{u} (f ⊗ₘ g) :=
  ((trivialFibrations SSet.{u}).arrow_mk_iso_iff
    (Arrow.isoMk (tensorProductIso A C) (tensorProductIso B D)
      (tensorProductIso_natural f g).symm)).2 (prodMap_trivialFibration f g hf hg)

end
end DaggerOriginalSimplicialTrivialFibrationTensor
