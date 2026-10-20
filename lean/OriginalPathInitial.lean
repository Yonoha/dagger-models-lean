import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.SimplicialThickening

universe u

namespace DaggerOriginalPathContraction

variable {J : Type u} [LinearOrder J]

instance pathThin (i j : J) : Quiver.IsThin (Path i j) := by
  intro P Q
  refine ⟨fun f g ↦ ?_⟩
  apply InducedCategory.hom_ext
  exact Subsingleton.elim _ _

/-- The literal endpoint subset in the original Mathlib Path category. -/
def initialPath (i j : J) (hij : i ≤ j) : Path i j where
  I := {i, j}
  left := by simp
  right := by simp
  left_le k hk := by
    rcases Set.mem_insert_iff.mp hk with rfl | hk
    · exact le_rfl
    · obtain rfl : k = j := Set.mem_singleton_iff.mp hk
      exact hij
  le_right k hk := by
    rcases Set.mem_insert_iff.mp hk with rfl | hk
    · exact hij
    · obtain rfl : k = j := Set.mem_singleton_iff.mp hk
      exact le_rfl

@[simp] theorem initialPath_I (i j : J) (hij : i ≤ j) :
    (initialPath i j hij).I = {i, j} := rfl

def initialTo (i j : J) (hij : i ≤ j) (P : Path i j) :
    initialPath i j hij ⟶ P :=
  ⟨⟨⟨by
    intro k hk
    rcases Set.mem_insert_iff.mp hk with rfl | hk
    · exact P.left
    · obtain rfl : k = j := Set.mem_singleton_iff.mp hk
      exact P.right⟩⟩⟩

theorem initialTo_unique (i j : J) (hij : i ≤ j) (P : Path i j)
    (f : initialPath i j hij ⟶ P) : f = initialTo i j hij P :=
  Subsingleton.elim _ _

def pathIsInitial (i j : J) (hij : i ≤ j) : IsInitial (initialPath i j hij) :=
  IsInitial.ofUniqueHom (initialTo i j hij) (initialTo_unique i j hij)

def initialNatTrans (i j : J) (hij : i ≤ j) :
    (Functor.const (Path i j)).obj (initialPath i j hij) ⟶ 𝟭 (Path i j) where
  app P := initialTo i j hij P
  naturality _ _ _ := Subsingleton.elim _ _

@[simp] theorem initialNatTrans_app (i j : J) (hij : i ≤ j) (P : Path i j) :
    (initialNatTrans i j hij).app P = initialTo i j hij P := rfl

@[simp] theorem initialPath_diagonal (i : J) :
    initialPath i i le_rfl = (𝟙 (SimplicialThickening.mk i)) := by
  apply Path.ext
  simp [initialPath]

theorem diagonal_path (i : J) (P : Path i i) :
    P = initialPath i i le_rfl := by
  apply Path.ext
  ext k
  constructor
  · intro hk
    have : k = i := le_antisymm (P.le_right k hk) (P.left_le k hk)
    simp [this, initialPath]
  · intro hk
    have : k = i := by simpa [initialPath] using hk
    simpa [this] using P.left

variable {K : Type u} [LinearOrder K]

@[simp] theorem initialPath_image (f : J →o K) (i j : J) (hij : i ≤ j) :
    (functorMap f (.mk i) (.mk j)).obj (initialPath i j hij) =
      initialPath (f i) (f j) (f.monotone hij) := by
  apply Path.ext
  change f '' {i, j} = {f i, f j}
  rw [Set.image_insert_eq, Set.image_singleton]

/-- The whole initial-to-object map is preserved, including noninjective direct images. -/
theorem initialTo_image (f : J →o K) (i j : J) (hij : i ≤ j) (P : Path i j) :
    (functorMap f (.mk i) (.mk j)).map (initialTo i j hij P) =
      eqToHom (initialPath_image f i j hij) ≫
        initialTo (f i) (f j) (f.monotone hij)
          ((functorMap f (.mk i) (.mk j)).obj P) := by
  apply InducedCategory.hom_ext
  exact Subsingleton.elim _ _

end DaggerOriginalPathContraction
