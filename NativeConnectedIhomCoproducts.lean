import NativeConnectedIhomFamily
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Existing connected-family isomorphisms give native coproduct preservation by internal Hom. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalClosed Simplicial
open DaggerOriginalProductGadget DaggerNativeConnectedIhomFamily
universe u
namespace DaggerNativeConnectedIhomCoproducts
noncomputable section

theorem comparison_square {I : Type u} (K : SSet.{u}) (X : I → SSet.{u}) :
    (familySigmaIso (fun i ↦ (ihom K).obj (X i))).hom ≫ familyIhomMap K X =
      sigmaComparison (ihom K) X ≫ (ihom K).map (familySigmaIso X).hom := by
  apply Limits.Sigma.hom_ext
  intro i
  simp only [← Category.assoc, familySigmaIso_ι, ι_comp_sigmaComparison]
  rw [← Functor.map_comp, familySigmaIso_ι]
  apply NatTrans.ext
  rfl

theorem comparison_isIso {I : Type u} (K : SSet.{u}) [Subsingleton K.π₀]
    (v : K _⦋0⦌) (X : I → SSet.{u}) : IsIso (sigmaComparison (ihom K) X) := by
  have := familyIhomMap_isIso K v X
  have : IsIso (sigmaComparison (ihom K) X ≫ (ihom K).map (familySigmaIso X).hom) := by
    rw [← comparison_square]
    infer_instance
  exact IsIso.of_isIso_comp_right (sigmaComparison (ihom K) X)
    ((ihom K).map (familySigmaIso X).hom)

theorem preserves_coproduct (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    {I : Type u} (X : I → SSet.{u}) : PreservesColimit (Discrete.functor X) (ihom K) := by
  have := comparison_isIso K v X
  exact PreservesCoproduct.of_iso_comparison (G := ihom K) (f := X)

theorem preserves_coproducts (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (I : Type u) : PreservesColimitsOfShape (Discrete I) (ihom K) := by
  have : ∀ X : I → SSet.{u}, PreservesColimit (Discrete.functor X) (ihom K) :=
    fun X ↦ preserves_coproduct K v X
  exact preservesColimitsOfShape_of_discrete _

end
end DaggerNativeConnectedIhomCoproducts
