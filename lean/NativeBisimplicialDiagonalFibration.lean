import NativeDiagonalHornMatrixLifting
import NativeDiagonalHornMatrixNaturality
import NativeBisimplicialBoxColumnLifting

/-! The full original Bousfield-Friedlander diagonal fibration theorem B.9. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialRelativeLifting DaggerNativeBisimplicialDiagonal
open DaggerNativeDiagonalHornMatrix DaggerNativeDiagonalHornMatrixFaces
open DaggerNativeDiagonalHornMatrixExtension DaggerNativeDiagonalHornMatrixNaturality
open DaggerNativeDiagonalHornMatrixLifting DaggerNativeBisimplicialBoxColumnLifting
open DaggerNativeBisimplicialBoxYoneda
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBisimplicialDiagonalFibration
noncomputable section

theorem matrixRestriction_simplex (n : ℕ) (k : Fin (n + 1)) (F : BiSSet.{u})
    (g : box (Δ[n] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ F) :
    matrixRestriction n k F
        (matrixInclusion n k ≫ boxMap (SSet.horn n k).ι (𝟙 (Δ[n] : SSet.{u})) ≫ g) =
      (SSet.horn n k).ι ≫ simplexRestriction n F g := by
  apply NatTrans.ext
  rfl

theorem diagonal_fibration {F G : BiSSet.{u}} (f : F ⟶ G) (hf : ReedyFibration f)
    (hc : ∀ v : SimplexCategoryᵒᵖ, Fibration (C := SSet.{u}) ((flipMap f).app v)) :
    Fibration (C := SSet.{u}) (diagonalFunctor.map f) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨m, ⟨k⟩⟩ := hi
  constructor
  intro a b sq
  let aa := matrixExtension k F a
  let bb := simplexExtension (m + 1) G b
  let j := boxMap (SSet.horn (m + 1) k).ι (𝟙 (Δ[m + 1] : SSet.{u}))
  have ss : CommSq aa (matrixInclusion (m + 1) k) f (j ≫ bb) := by
    constructor
    apply (matrixRestriction_bijective (m + 1) k G).injective
    dsimp only [aa, bb, j]
    rw [matrixRestriction_post, matrixExtension_restrict,
      matrixRestriction_simplex, simplexExtension_restrict]
    exact sq.w
  have : HasLiftingProperty (matrixInclusion (m + 1) k) f := matrix_lifting _ _ f hf
  have tt : CommSq ss.lift j f bb := ⟨ss.fac_right⟩
  have : HasLiftingProperty j f := box_horn_lifting f hc m k (m + 1)
  refine ⟨simplexRestriction (m + 1) F tt.lift, ?_, ?_⟩
  · have hw : matrixInclusion (m + 1) k ≫ j ≫ tt.lift = aa := by
      rw [tt.fac_left]
      exact ss.fac_left
    have he := congrArg (matrixRestriction (m + 1) k F) hw
    dsimp only [j] at he
    rw [matrixRestriction_simplex] at he
    exact he.trans (matrixExtension_restrict k F a)
  · have he := congrArg (simplexRestriction (m + 1) G) tt.fac_right
    rw [simplexRestriction_post] at he
    exact he.trans (simplexExtension_restrict (m + 1) G b)

end
end DaggerNativeBisimplicialDiagonalFibration
