import NativeIhomQuasicategories
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Native internal Hom currying across the original tensor product

Use the two actual closed adjunctions and uniqueness of right adjoints. The full
comparison is an isomorphism of simplicial sets, with the exact original source,
target, associator and evaluation. Naturality in the domain map is proved explicitly.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed
universe u
namespace DaggerNativeIhomTensorComparison
noncomputable section

/-- The original composite closed adjunction, transported through the native associator. -/
def tensorAdjunction (K A : SSet.{u}) :
    tensorLeft (K ⊗ A) ⊣ ihom K ⋙ ihom A :=
  (tensorClosed (inferInstance : Closed K) (inferInstance : Closed A)).adj

/-- Compare the full chosen native ihom with the full composite native ihom functor. -/
def comparisonNatIso (K A : SSet.{u}) : ihom (K ⊗ A) ≅ ihom K ⋙ ihom A :=
  (ihom.adjunction (K ⊗ A)).rightAdjointUniq (tensorAdjunction K A)

def comparisonIso (K A Z : SSet.{u}) :
    (ihom (K ⊗ A)).obj Z ≅ (ihom A).obj ((ihom K).obj Z) :=
  (comparisonNatIso K A).app Z

/-- The entire comparison is characterized by two original uncurrying operations. -/
theorem comparison_uncurry (K A Z : SSet.{u}) :
    MonoidalClosed.uncurry (MonoidalClosed.uncurry (comparisonIso K A Z).hom) =
      (α_ K A ((ihom (K ⊗ A)).obj Z)).inv ≫ (ihom.ev (K ⊗ A)).app Z := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (ihom.adjunction (K ⊗ A)) (tensorAdjunction K A) Z
  change (α_ K A ((ihom (K ⊗ A)).obj Z)).hom ≫
    MonoidalClosed.uncurry (MonoidalClosed.uncurry (comparisonIso K A Z).hom) =
      (ihom.ev (K ⊗ A)).app Z at h
  exact (Iso.eq_inv_comp _).2 h

/-- Full precomposition agrees with restriction in the second native domain parameter. -/
theorem pre_naturality (K Z : SSet.{u}) {A B : SSet.{u}} (f : A ⟶ B) :
    (MonoidalClosed.pre (K ◁ f)).app Z ≫ (comparisonIso K A Z).hom =
      (comparisonIso K B Z).hom ≫ (MonoidalClosed.pre f).app ((ihom K).obj Z) := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left,
    comparison_uncurry, comparison_uncurry]
  rw [MonoidalCategory.associator_inv_naturality_right_assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev,
    ← MonoidalCategory.associator_inv_naturality_middle_assoc]

end
end DaggerNativeIhomTensorComparison
