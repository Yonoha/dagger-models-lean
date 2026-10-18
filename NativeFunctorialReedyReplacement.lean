import NativeReedyFactorization
import NativeReedyFibrantHorizontalMapping

/-! Actual functorial Reedy fibrant replacement preserves every original diagram by its unit. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedySmallObject
open DaggerNativeReedyFactorization DaggerNativeReedyFibrantHorizontalMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFunctorialReedyReplacement
noncomputable section

def terminalArrowFunctor : BiSSet.{u} ⥤ Arrow BiSSet.{u} where
  obj X := Arrow.mk (toTerminal X)
  map f := Arrow.homMk f (𝟙 terminalBi) (by
    change f ≫ toTerminal _ = toTerminal _ ≫ 𝟙 terminalBi
    rw [Category.comp_id]
    apply NatTrans.ext
    funext h
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  map_id _ := by apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · simp

def replacement : BiSSet.{u} ⥤ BiSSet.{u} := terminalArrowFunctor ⋙ factorizationData.Z

def unit : 𝟭 BiSSet.{u} ⟶ replacement where
  app X := inclusion (toTerminal X)
  naturality _ _ f := (inclusion_natural (terminalArrowFunctor.map f)).symm

theorem replacement_reedy (X : BiSSet.{u}) : ReedyFibrant (replacement.obj X) := by
  have he : projection (toTerminal X) = toTerminal (replacement.obj X) := by
    apply NatTrans.ext
    funext h
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  unfold ReedyFibrant
  rw [← he]
  exact projection_reedy (toTerminal X)

theorem unit_row_trivial (X : BiSSet.{u}) (h : SimplexCategoryᵒᵖ) :
    trivialCofibrations SSet.{u} ((unit.app X).app h) :=
  inclusion_row_trivial (toTerminal X) h

theorem unit_row_weak (X : BiSSet.{u}) (h : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((unit.app X).app h) :=
  ((mem_trivialCofibrations_iff _).mp (unit_row_trivial X h)).2

theorem replacement_row_Kan (X : BiSSet.{u}) (h : SimplexCategoryᵒᵖ) :
    IsFibrant ((replacement.obj X).obj h) := by
  cases h with
  | op h =>
    induction h using SimplexCategory.rec with
    | h m =>
      have : IsFibrant (horizontalMapping (Δ[m] : SSet.{u}) (replacement.obj X)) :=
        mapping_isFibrant (replacement.obj X) (replacement_reedy X) Δ[m]
      exact isFibrant_of_fibration (horizontalSimplexIso (replacement.obj X) m).inv

end
end DaggerNativeFunctorialReedyReplacement
