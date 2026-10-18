import OriginalPathInitial
import NerveHomotopy
import TopCatModelCategory.SSet.Contractible

set_option autoImplicit false

open CategoryTheory CategoryTheory.Category Limits MonoidalCategory Simplicial Opposite
open CategoryTheory.SimplicialThickening

universe u

namespace DaggerOriginalPathContraction

noncomputable section

variable {J : Type u} [LinearOrder J]

abbrev pathNerve (i j : J) : SSet.{u} := nerve (Path i j)

def center (i j : J) (hij : i ≤ j) : (pathNerve i j) _⦋0⦌ :=
  ComposableArrows.mk₀ (initialPath i j hij)

theorem initial_nerve_const (i j : J) (hij : i ≤ j) :
    nerveMap ((Functor.const (Path i j)).obj (initialPath i j hij)) =
      SSet.const (X := pathNerve i j) (center i j hij) := by
  apply SSet.hom_ext
  intro n
  funext F
  apply nerve.ext_of_isThin
  rfl

theorem initial_nerve_id (i j : J) :
    nerveMap (𝟭 (Path i j)) = 𝟙 (pathNerve i j) := by
  apply SSet.hom_ext
  intro n
  funext F
  apply nerve.ext_of_isThin
  rfl

/-- The existing nerve natural-transformation homotopy, with literal endpoint maps. -/
def contraction (i j : J) (hij : i ≤ j) :
    SSet.Homotopy (SSet.const (X := pathNerve i j) (center i j hij))
      (𝟙 (pathNerve i j)) :=
  (DaggerNerveHomotopy.natTransHomotopy (initialNatTrans i j hij)).congr
    (initial_nerve_const i j hij) (initial_nerve_id i j)

@[simp] theorem contraction_map (i j : J) (hij : i ≤ j) :
    (contraction i j hij).h = DaggerNerveHomotopy.natTransMap (initialNatTrans i j hij) := rfl

theorem contraction_zero (i j : J) (hij : i ≤ j) :
    SSet.ι₀ ≫ (contraction i j hij).h = SSet.const (center i j hij) :=
  (contraction i j hij).h₀

theorem contraction_one (i j : J) (hij : i ≤ j) :
    SSet.ι₁ ≫ (contraction i j hij).h = 𝟙 (pathNerve i j) :=
  (contraction i j hij).h₁

/-- Full all-time simplex formula, before any realization or quotient. -/
theorem contraction_obj (i j : J) (hij : i ≤ j) (n : SimplexCategoryᵒᵖ)
    (F : (pathNerve i j).obj n) (t : (SSet.stdSimplex.obj ⦋1⦌).obj n)
    (s : Fin (n.unop.len + 1)) :
    (((contraction i j hij).h.app n (F, t)).obj s) =
      if (SSet.stdSimplex.objEquiv t).toOrderHom s = 0 then initialPath i j hij
        else F.obj s := by
  change ((ComposableArrows.mk₁ (initialNatTrans i j hij)).obj
    ((SSet.stdSimplex.objEquiv t).toOrderHom s)).obj (F.obj s) = _
  generalize (SSet.stdSimplex.objEquiv t).toOrderHom s = r
  fin_cases r <;> rfl

/-- All arrows of every time simplex are the original subset-inclusion morphisms. -/
theorem contraction_map_unique (i j : J) (hij : i ≤ j) (n : SimplexCategoryᵒᵖ)
    (F : (pathNerve i j).obj n) (t : (SSet.stdSimplex.obj ⦋1⦌).obj n)
    {s s' : Fin (n.unop.len + 1)} (a : s ⟶ s')
    (b : ((contraction i j hij).h.app n (F, t)).obj s ⟶
      ((contraction i j hij).h.app n (F, t)).obj s') :
    ((contraction i j hij).h.app n (F, t)).map a = b :=
  Subsingleton.elim _ _

def pathContractible (i j : J) (hij : i ≤ j) : SSet.Contractible (pathNerve i j) where
  pt := center i j hij
  h := contraction i j hij

variable {K : Type u} [LinearOrder K]

@[simp] theorem center_image (f : J →o K) (i j : J) (hij : i ≤ j) :
    (nerveMap (functorMap f (.mk i) (.mk j))).app _ (center i j hij) =
      center (f i) (f j) (f.monotone hij) := by
  unfold center
  rw [nerveMap_app_mk₀, initialPath_image]

/-- The full contraction commutes with every original monotone direct-image map. -/
theorem contraction_natural (f : J →o K) (i j : J) (hij : i ≤ j) :
    (nerveMap (functorMap f (.mk i) (.mk j)) ⊗ₘ
        𝟙 (SSet.stdSimplex.obj ⦋1⦌)) ≫
      (contraction (f i) (f j) (f.monotone hij)).h =
    (contraction i j hij).h ≫ nerveMap (functorMap f (.mk i) (.mk j)) := by
  apply SSet.hom_ext
  intro n
  funext p
  apply nerve.ext_of_isThin
  funext s
  change (((contraction (f i) (f j) (f.monotone hij)).h.app n
      ((nerveMap (functorMap f (.mk i) (.mk j))).app n p.1, p.2)).obj s) = _
  rw [contraction_obj]
  change (if (SSet.stdSimplex.objEquiv p.2).toOrderHom s = 0 then
      initialPath (f i) (f j) (f.monotone hij) else
      (functorMap f (.mk i) (.mk j)).obj (p.1.obj s)) =
    (functorMap f (.mk i) (.mk j)).obj
      (((contraction i j hij).h.app n (p.1, p.2)).obj s)
  rw [contraction_obj]
  split_ifs
  · exact (initialPath_image f i j hij).symm
  · rfl

end

end DaggerOriginalPathContraction

namespace DaggerOriginalPathContraction

open CategoryTheory CategoryTheory.Category Limits MonoidalCategory Simplicial Opposite
open CategoryTheory.SimplicialThickening

noncomputable section

variable {J : Type u} [LinearOrder J]

theorem contraction_obj_I (i j : J) (hij : i ≤ j) (n : SimplexCategoryᵒᵖ)
    (F : (pathNerve i j).obj n) (t : (SSet.stdSimplex.obj ⦋1⦌).obj n)
    (s : Fin (n.unop.len + 1)) :
    (((contraction i j hij).h.app n (F, t)).obj s).I =
      if (SSet.stdSimplex.objEquiv t).toOrderHom s = 0 then {i, j}
        else (F.obj s).I := by
  rw [contraction_obj]
  split_ifs <;> rfl

/-- Compatibility with every simplex operator, including degeneracies that collapse endpoints. -/
theorem contraction_simplex (i j : J) (hij : i ≤ j) {m n : SimplexCategoryᵒᵖ}
    (a : m ⟶ n) (F : (pathNerve i j).obj m)
    (t : (SSet.stdSimplex.obj ⦋1⦌).obj m) :
    (pathNerve i j).map a ((contraction i j hij).h.app m (F, t)) =
      (contraction i j hij).h.app n
        ((pathNerve i j).map a F, (SSet.stdSimplex.obj ⦋1⦌).map a t) := rfl

/-- Coincident endpoints still use the literal original Path and the literal nerve map. -/
theorem contraction_diagonal (i : J) :
    (contraction i i le_rfl).h =
      CartesianMonoidalCategory.fst (pathNerve i i) (SSet.stdSimplex.obj ⦋1⦌) := by
  apply SSet.hom_ext
  intro n
  funext p
  apply nerve.ext_of_isThin
  funext s
  exact (diagonal_path i _).trans (diagonal_path i _).symm

end

end DaggerOriginalPathContraction
