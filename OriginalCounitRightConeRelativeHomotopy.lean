import OriginalCounitRightConeRelativeHomotopyOrder

/-!
# The actual relative homotopy on the original right cone

The prism on the large simplex is constant after passage to the collapsed
initial face. Currying this compatible pair, applying the *original* cone
pushout descent, and uncurrying constructs a map on the literal cone product.
This source-only candidate asserts no Joyal or geometric weak equivalence.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeRelativeHomotopy

universe u

namespace DaggerOriginalCounitRightConeRelativeHomotopy

noncomputable section

/-- The actual last-face map inserts each vertex before the final vertex. -/
theorem face_app (n d : ℕ) (x : (Δ[n] : SSet.{u}) _⦋d⦌)
    (i : Fin (d + 1)) :
    (face.{u} n).app (op ⦋d⦌) x i = (x i).castSucc := by
  change (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom (x i) =
    (x i).castSucc
  simp [SimplexCategory.δ, Fin.succAbove_last]

/-- The whole prism map respects the actual attaching face. -/
theorem simplexPrism_face (n : ℕ) :
    (face.{u} n ▷ (Δ[1] : SSet.{u})) ≫ simplexPrism.{u} n 1 =
      simplexPrism.{u} n 0 ≫ face.{u} n := by
  apply NatTrans.ext
  funext q z
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d =>
    apply SSet.stdSimplex.ext
    intro i
    simpa only [SSet.comp_app, CategoryTheory.types_comp_apply,
      SSet.whiskerRight_app_apply,
      simplexPrism_app, face_app] using
      prismOrder_face n (z.1 i) (z.2 i)

/-- The large prism becomes constant on the collapsed attaching face. -/
theorem face_prism_constant (n : ℕ) :
    (face.{u} n ▷ (Δ[1] : SSet.{u})) ≫ simplexPrism.{u} n 1 ≫
        simplexIncl.{u} n =
      SSet.stdSimplex.isTerminalObj₀.from ((Δ[n] ⊗ Δ[1]) : SSet.{u}) ≫
        baseIncl.{u} n := by
  calc
    _ = simplexPrism.{u} n 0 ≫ face.{u} n ≫ simplexIncl.{u} n := by
      simp only [← Category.assoc, simplexPrism_face]
    _ = simplexPrism.{u} n 0 ≫ collapse.{u} n ≫ baseIncl.{u} n := by
      simp only [← Category.assoc, face_eq_collapse]
    _ = SSet.stdSimplex.isTerminalObj₀.from ((Δ[n] ⊗ Δ[1]) : SSet.{u}) ≫
          baseIncl.{u} n := by
      have h : simplexPrism.{u} n 0 ≫ collapse.{u} n =
          SSet.stdSimplex.isTerminalObj₀.from ((Δ[n] ⊗ Δ[1]) : SSet.{u}) :=
        SSet.stdSimplex.ext₀
      simpa only [← Category.assoc] using
        congrArg (fun f : ((Δ[n] ⊗ Δ[1]) : SSet.{u}) ⟶ Δ[0] ↦
          f ≫ baseIncl.{u} n) h

private def largeSwapped (n : ℕ) :
    (Δ[1] ⊗ Δ[n + 1] : SSet.{u}) ⟶ cone.{u} n :=
  (β_ (Δ[1] : SSet.{u}) Δ[n + 1]).hom ≫
    simplexPrism.{u} n 1 ≫ simplexIncl.{u} n

private def baseSwapped (n : ℕ) :
    (Δ[1] ⊗ Δ[0] : SSet.{u}) ⟶ cone.{u} n :=
  (β_ (Δ[1] : SSet.{u}) Δ[0]).hom ≫
    SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ Δ[1]) : SSet.{u}) ≫
      baseIncl.{u} n

/-- The braided large prism and constant formal alpha agree on the face. -/
private theorem swapped_compat (n : ℕ) :
    ((Δ[1] : SSet.{u}) ◁ face.{u} n) ≫ largeSwapped.{u} n =
      ((Δ[1] : SSet.{u}) ◁ collapse.{u} n) ≫ baseSwapped.{u} n := by
  calc
    _ = (β_ (Δ[1] : SSet.{u}) Δ[n]).hom ≫
          (face.{u} n ▷ (Δ[1] : SSet.{u})) ≫
          simplexPrism.{u} n 1 ≫ simplexIncl.{u} n := by
      simp only [largeSwapped, ← Category.assoc]
      rw [BraidedCategory.braiding_naturality_right]
    _ = (β_ (Δ[1] : SSet.{u}) Δ[n]).hom ≫
          SSet.stdSimplex.isTerminalObj₀.from ((Δ[n] ⊗ Δ[1]) : SSet.{u}) ≫
            baseIncl.{u} n := by
      rw [face_prism_constant]
    _ = ((Δ[1] : SSet.{u}) ◁ collapse.{u} n) ≫ baseSwapped.{u} n := by
      have h :
          (β_ (Δ[1] : SSet.{u}) Δ[n]).hom ≫
              SSet.stdSimplex.isTerminalObj₀.from
                ((Δ[n] ⊗ Δ[1]) : SSet.{u}) =
            ((Δ[1] : SSet.{u}) ◁ collapse.{u} n) ≫
              (β_ (Δ[1] : SSet.{u}) Δ[0]).hom ≫
                SSet.stdSimplex.isTerminalObj₀.from
                  ((Δ[0] ⊗ Δ[1]) : SSet.{u}) :=
        SSet.stdSimplex.ext₀
      simpa only [baseSwapped, Category.assoc] using
        congrArg (fun f ↦ f ≫ baseIncl.{u} n) h

private theorem curried_compat (n : ℕ) :
    face.{u} n ≫ MonoidalClosed.curry (largeSwapped.{u} n) =
      collapse.{u} n ≫ MonoidalClosed.curry (baseSwapped.{u} n) := by
  calc
    _ = MonoidalClosed.curry
          (((Δ[1] : SSet.{u}) ◁ face.{u} n) ≫ largeSwapped.{u} n) :=
      (MonoidalClosed.curry_natural_left _ _).symm
    _ = MonoidalClosed.curry
          (((Δ[1] : SSet.{u}) ◁ collapse.{u} n) ≫ baseSwapped.{u} n) :=
      congrArg MonoidalClosed.curry (swapped_compat.{u} n)
    _ = _ := MonoidalClosed.curry_natural_left _ _

/-- Descent to the internal path object uses the literal cone pushout. -/
def curriedHomotopy (n : ℕ) :
    cone.{u} n ⟶ ((Δ[1] : SSet.{u}) ⟶[SSet.{u}] cone.{u} n) :=
  desc.{u} n (MonoidalClosed.curry (largeSwapped.{u} n))
    (MonoidalClosed.curry (baseSwapped.{u} n)) (curried_compat.{u} n)

/-- The actual simplicial homotopy on the chosen right cone. -/
def relativeHomotopy (n : ℕ) :
    (cone.{u} n ⊗ Δ[1] : SSet.{u}) ⟶ cone.{u} n :=
  (β_ (cone.{u} n) (Δ[1] : SSet.{u})).hom ≫
    MonoidalClosed.uncurry (curriedHomotopy.{u} n)

/-- On the original large-simplex leg this is exactly the ordinal prism. -/
theorem simplexIncl_relativeHomotopy (n : ℕ) :
    (simplexIncl.{u} n ▷ (Δ[1] : SSet.{u})) ≫
        relativeHomotopy.{u} n =
      simplexPrism.{u} n 1 ≫ simplexIncl.{u} n := by
  calc
    _ = (β_ (Δ[n + 1] : SSet.{u}) Δ[1]).hom ≫
          ((Δ[1] : SSet.{u}) ◁ simplexIncl.{u} n) ≫
          MonoidalClosed.uncurry (curriedHomotopy.{u} n) := by
      simp only [relativeHomotopy, ← Category.assoc]
      rw [BraidedCategory.braiding_naturality_left]
    _ = (β_ (Δ[n + 1] : SSet.{u}) Δ[1]).hom ≫
          MonoidalClosed.uncurry
            (simplexIncl.{u} n ≫ curriedHomotopy.{u} n) := by
      rw [MonoidalClosed.uncurry_natural_left]
    _ = (β_ (Δ[n + 1] : SSet.{u}) Δ[1]).hom ≫ largeSwapped.{u} n := by
      rw [curriedHomotopy, simplexIncl_desc, MonoidalClosed.uncurry_curry]
    _ = simplexPrism.{u} n 1 ≫ simplexIncl.{u} n := by
      simp only [largeSwapped, ← Category.assoc, SymmetricCategory.symmetry,
        Category.id_comp]

/-- On the original collapsed-face leg the homotopy is constantly alpha. -/
theorem baseIncl_relativeHomotopy (n : ℕ) :
    (baseIncl.{u} n ▷ (Δ[1] : SSet.{u})) ≫ relativeHomotopy.{u} n =
      SSet.stdSimplex.isTerminalObj₀.from ((Δ[0] ⊗ Δ[1]) : SSet.{u}) ≫
        baseIncl.{u} n := by
  calc
    _ = (β_ (Δ[0] : SSet.{u}) Δ[1]).hom ≫
          ((Δ[1] : SSet.{u}) ◁ baseIncl.{u} n) ≫
          MonoidalClosed.uncurry (curriedHomotopy.{u} n) := by
      simp only [relativeHomotopy, ← Category.assoc]
      rw [BraidedCategory.braiding_naturality_left]
    _ = (β_ (Δ[0] : SSet.{u}) Δ[1]).hom ≫
          MonoidalClosed.uncurry
            (baseIncl.{u} n ≫ curriedHomotopy.{u} n) := by
      rw [MonoidalClosed.uncurry_natural_left]
    _ = (β_ (Δ[0] : SSet.{u}) Δ[1]).hom ≫ baseSwapped.{u} n := by
      rw [curriedHomotopy, baseIncl_desc, MonoidalClosed.uncurry_curry]
    _ = SSet.stdSimplex.isTerminalObj₀.from
          ((Δ[0] ⊗ Δ[1]) : SSet.{u}) ≫ baseIncl.{u} n := by
      simp only [baseSwapped, ← Category.assoc, SymmetricCategory.symmetry,
        Category.id_comp]

end

end DaggerOriginalCounitRightConeRelativeHomotopy
