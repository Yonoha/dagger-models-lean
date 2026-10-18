import NativeFunctorialReedyReplacement

/-! Functorial relative replacement lies over the actual Reedy fibrant replacement of the base. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedyFactorization
open DaggerNativeReedyFibrantHorizontalMapping DaggerNativeReedyGeneratingLifting
open DaggerNativeReedySmallObject DaggerNativeFunctorialReedyReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyRelativeReplacement
noncomputable section

def pushedArrow : Arrow BiSSet.{u} ⥤ Arrow BiSSet.{u} where
  obj f := Arrow.mk (f.hom ≫ unit.app f.right)
  map s := Arrow.homMk s.left (replacement.map s.right) (by
    change s.left ≫ (_ ≫ unit.app _) = (_ ≫ unit.app _) ≫ replacement.map s.right
    have hw := s.w
    change s.left ≫ _ = _ ≫ s.right at hw
    have hu := unit.naturality s.right
    change s.right ≫ unit.app _ = unit.app _ ≫ replacement.map s.right at hu
    rw [← Category.assoc, hw, Category.assoc, hu, ← Category.assoc])
  map_id f := by
    apply Arrow.hom_ext
    · rfl
    · exact replacement.map_id f.right
  map_comp s t := by
    apply Arrow.hom_ext
    · rfl
    · exact replacement.map_comp s.right t.right

def projectedArrow : Arrow BiSSet.{u} ⥤ Arrow BiSSet.{u} where
  obj f := Arrow.mk (projection f.hom)
  map s := Arrow.homMk (DaggerNativeReedyFactorization.map s) s.right (projection_natural s)
  map_id f := by
    apply Arrow.hom_ext
    · exact DaggerNativeReedyFactorization.map_id f.hom
    · rfl
  map_comp s t := by
    apply Arrow.hom_ext
    · exact DaggerNativeReedyFactorization.map_comp s t
    · rfl

def relativeReplacement : Arrow BiSSet.{u} ⥤ Arrow BiSSet.{u} := pushedArrow ⋙ projectedArrow

def totalUnit (f : Arrow BiSSet.{u}) : f.left ⟶ (relativeReplacement.obj f).left :=
  inclusion (f.hom ≫ unit.app f.right)

def baseUnit (f : Arrow BiSSet.{u}) : f.right ⟶ (relativeReplacement.obj f).right :=
  unit.app f.right

theorem unit_square (f : Arrow BiSSet.{u}) :
    totalUnit f ≫ (relativeReplacement.obj f).hom = f.hom ≫ baseUnit f :=
  fac (f.hom ≫ unit.app f.right)

theorem totalUnit_natural {f g : Arrow BiSSet.{u}} (s : f ⟶ g) :
    totalUnit f ≫ (relativeReplacement.map s).left = s.left ≫ totalUnit g :=
  inclusion_natural (pushedArrow.map s)

theorem baseUnit_natural {f g : Arrow BiSSet.{u}} (s : f ⟶ g) :
    baseUnit f ≫ (relativeReplacement.map s).right = s.right ≫ baseUnit g :=
  (unit.naturality s.right).symm

theorem totalUnit_row_trivial (f : Arrow BiSSet.{u}) (h : SimplexCategoryᵒᵖ) :
    trivialCofibrations SSet.{u} ((totalUnit f).app h) :=
  inclusion_row_trivial (f.hom ≫ unit.app f.right) h

theorem baseUnit_row_trivial (f : Arrow BiSSet.{u}) (h : SimplexCategoryᵒᵖ) :
    trivialCofibrations SSet.{u} ((baseUnit f).app h) := unit_row_trivial f.right h

theorem projection_reedy (f : Arrow BiSSet.{u}) :
    ReedyFibration (relativeReplacement.obj f).hom :=
  DaggerNativeReedyFactorization.projection_reedy (f.hom ≫ unit.app f.right)

theorem base_reedy (f : Arrow BiSSet.{u}) : ReedyFibrant (relativeReplacement.obj f).right :=
  replacement_reedy f.right

theorem total_reedy (f : Arrow BiSSet.{u}) : ReedyFibrant (relativeReplacement.obj f).left := by
  let q := (relativeReplacement.obj f).hom
  have hq : J.rlp q := reedy_implies_rlp q (projection_reedy f)
  have hb : J.rlp (toTerminal (relativeReplacement.obj f).right) :=
    reedy_implies_rlp _ (base_reedy f)
  have hc : J.rlp (q ≫ toTerminal (relativeReplacement.obj f).right) :=
    J.rlp.comp_mem q _ hq hb
  have he : q ≫ toTerminal (relativeReplacement.obj f).right =
      toTerminal (relativeReplacement.obj f).left := by
    apply NatTrans.ext
    funext h
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  unfold ReedyFibrant
  rw [← he]
  exact rlp_implies_reedy _ hc

theorem reedy_rows_Kan (X : BiSSet.{u}) (hX : ReedyFibrant X) (h : SimplexCategoryᵒᵖ) :
    IsFibrant (X.obj h) := by
  cases h with
  | op h =>
    induction h using SimplexCategory.rec with
    | h m =>
      have : IsFibrant (horizontalMapping (Δ[m] : SSet.{u}) X) := mapping_isFibrant X hX Δ[m]
      exact isFibrant_of_fibration (horizontalSimplexIso X m).inv

theorem total_rows_Kan (f : Arrow BiSSet.{u}) (h : SimplexCategoryᵒᵖ) :
    IsFibrant ((relativeReplacement.obj f).left.obj h) := reedy_rows_Kan _ (total_reedy f) h

theorem base_rows_Kan (f : Arrow BiSSet.{u}) (h : SimplexCategoryᵒᵖ) :
    IsFibrant ((relativeReplacement.obj f).right.obj h) := replacement_row_Kan f.right h

end
end DaggerNativeReedyRelativeReplacement
