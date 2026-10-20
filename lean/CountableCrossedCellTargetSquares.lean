import CountableCrossedInverseTargetSquare

/-! Every descended raw cell retains its exact ORIGINAL chosen global image. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerNativeJoyalWeakSimplexInverse DaggerRelativeInverseLadderData
open DaggerCountableArrowStageDiagrams DaggerCountableCrossedCellColimit
open DaggerInverseTriangleCellFamily DaggerRectangularInverseWitnessData
open DaggerNativeEndomorphismSimplexMaps
universe u v w
namespace DaggerCountableCrossedCellTargetSquares
local instance nativeBraiding : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory
local instance tensorRightPreserves (K : SSet.{u}) :
    PreservesColimitsOfShape ℕ (tensorRight K) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

variable {C : Type w} [Category.{v} C] [HasColimitsOfShape ℕ C]
  (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape ℕ R]
  {D : ℕ ⥤ Arrow C} (c : Cocone D) (e : Ladder R D)

theorem left_target (hc : IsColimit c) (c₀ : Cocone D)
    (d : SimplexInverseData (R.map c₀.pt.hom)) (he : Over R D e c₀ d) (r : Kind) :
    Square (R.map (hc.desc c₀).left) (R.map (hc.desc c₀).left)
      (leftCell R c e r hc) (DaggerRawIsoTriangleCells.cell d.left r) := by
  apply (square_iff_tensor_map _ _ _ _ _).2
  rw [leftCell, Equiv.apply_symm_apply]
  apply (isColimitOfPreserves (tensorRight Δ[r.degree]) (leftIsColimit R c hc)).hom_ext
  intro n
  change (R.map (c.ι.app n).left ▷ Δ[r.degree]) ≫
      ((isColimitOfPreserves (tensorRight Δ[r.degree]) (leftIsColimit R c hc)).desc
        (leftCellCocone R c e r) ≫ R.map (hc.desc c₀).left) =
    (R.map (c.ι.app n).left ▷ Δ[r.degree]) ≫
      (R.map (hc.desc c₀).left ▷ Δ[r.degree] ≫
        simplexHomEquiv (R.obj c₀.pt.left) (R.obj c₀.pt.left) r.degree
          (DaggerRawIsoTriangleCells.cell d.left r))
  have hfac : R.map (c.ι.app n).left ▷ Δ[r.degree] ≫
      (isColimitOfPreserves (tensorRight Δ[r.degree]) (leftIsColimit R c hc)).desc
        (leftCellCocone R c e r) =
    simplexHomEquiv (R.obj (D.obj n).left) (R.obj (D.obj (n + 1)).left) r.degree
      (DaggerRawIsoTriangleCells.cell (e.data n).left r) ≫
        R.map (c.ι.app (n + 1)).left :=
    (isColimitOfPreserves (tensorRight Δ[r.degree]) (leftIsColimit R c hc)).fac
      (leftCellCocone R c e r) n
  rw [← Category.assoc, hfac]
  change (simplexHomEquiv (R.obj (D.obj n).left) (R.obj (D.obj (n + 1)).left) r.degree
      (DaggerRawIsoTriangleCells.cell (e.data n).left r) ≫
        R.map (c.ι.app (n + 1)).left) ≫ R.map (hc.desc c₀).left = _
  have hleg (m : ℕ) : R.map (c.ι.app m).left ≫ R.map (hc.desc c₀).left =
      R.map (c₀.ι.app m).left := by
    rw [← R.map_comp]
    exact congrArg (fun f : D.obj m ⟶ c₀.pt ↦ R.map f.left) (hc.fac c₀ m)
  rw [Category.assoc, hleg]
  have h := (square_iff_tensor_map _ _ _ _ _).1 (he.left_fac n r)
  exact h.trans (by
    rw [← Category.assoc, ← comp_whiskerRight, hleg]
    rfl)

theorem right_target (hc : IsColimit c) (c₀ : Cocone D)
    (d : SimplexInverseData (R.map c₀.pt.hom)) (he : Over R D e c₀ d) (r : Kind) :
    Square (R.map (hc.desc c₀).right) (R.map (hc.desc c₀).right)
      (rightCell R c e r hc) (DaggerRawIsoTriangleCells.cell d.right r) := by
  apply (square_iff_tensor_map _ _ _ _ _).2
  rw [rightCell, Equiv.apply_symm_apply]
  apply (isColimitOfPreserves (tensorRight Δ[r.degree]) (rightIsColimit R c hc)).hom_ext
  intro n
  change (R.map (c.ι.app n).right ▷ Δ[r.degree]) ≫
      ((isColimitOfPreserves (tensorRight Δ[r.degree]) (rightIsColimit R c hc)).desc
        (rightCellCocone R c e r) ≫ R.map (hc.desc c₀).right) =
    (R.map (c.ι.app n).right ▷ Δ[r.degree]) ≫
      (R.map (hc.desc c₀).right ▷ Δ[r.degree] ≫
        simplexHomEquiv (R.obj c₀.pt.right) (R.obj c₀.pt.right) r.degree
          (DaggerRawIsoTriangleCells.cell d.right r))
  have hfac : R.map (c.ι.app n).right ▷ Δ[r.degree] ≫
      (isColimitOfPreserves (tensorRight Δ[r.degree]) (rightIsColimit R c hc)).desc
        (rightCellCocone R c e r) =
    simplexHomEquiv (R.obj (D.obj n).right) (R.obj (D.obj (n + 1)).right) r.degree
      (DaggerRawIsoTriangleCells.cell (e.data n).right r) ≫
        R.map (c.ι.app (n + 1)).right :=
    (isColimitOfPreserves (tensorRight Δ[r.degree]) (rightIsColimit R c hc)).fac
      (rightCellCocone R c e r) n
  rw [← Category.assoc, hfac]
  change (simplexHomEquiv (R.obj (D.obj n).right) (R.obj (D.obj (n + 1)).right) r.degree
      (DaggerRawIsoTriangleCells.cell (e.data n).right r) ≫
        R.map (c.ι.app (n + 1)).right) ≫ R.map (hc.desc c₀).right = _
  have hleg (m : ℕ) : R.map (c.ι.app m).right ≫ R.map (hc.desc c₀).right =
      R.map (c₀.ι.app m).right := by
    rw [← R.map_comp]
    exact congrArg (fun f : D.obj m ⟶ c₀.pt ↦ R.map f.right) (hc.fac c₀ m)
  rw [Category.assoc, hleg]
  have h := (square_iff_tensor_map _ _ _ _ _).1 (he.right_fac n r)
  exact h.trans (by
    rw [← Category.assoc, ← comp_whiskerRight, hleg]
    rfl)

end DaggerCountableCrossedCellTargetSquares
