import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.PathCategory.Basic

/-! Total native path length gives the generator spine of any free-category nerve. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
universe u
namespace DaggerNativeFreePathNerveWeight
noncomputable section

variable {V : Type u} [Quiver.{u + 1} V]

def totalPath {n : ℕ} (c : ComposableArrows (Paths V) n) :
    Quiver.Path (show V from c.obj 0) (show V from c.obj (Fin.last n)) :=
  c.map (homOfLE (Fin.zero_le (Fin.last n)))

def weight {n : ℕ} (c : ComposableArrows (Paths V) n) : ℕ := (totalPath c).length

theorem segment_length_le {n : ℕ} (c : ComposableArrows (Paths V) n)
    (i j : Fin (n + 1)) (h : i ≤ j) :
    (c.map (homOfLE h)).length ≤ weight c := by
  have he : (c.map (homOfLE (Fin.zero_le i))).comp
      ((c.map (homOfLE h)).comp (c.map (homOfLE (Fin.le_last j)))) = totalPath c := by
    change c.map _ ≫ c.map _ ≫ c.map _ = c.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  have hl := congrArg Quiver.Path.length he
  rw [Quiver.Path.length_comp, Quiver.Path.length_comp] at hl
  change _ ≤ (totalPath c).length
  omega

theorem weight_whisker_le {m n : ℕ} (c : ComposableArrows (Paths V) n)
    (φ : Fin (m + 1) ⥤ Fin (n + 1)) : weight (φ ⋙ c) ≤ weight c := by
  change (c.map (φ.map (homOfLE (Fin.zero_le (Fin.last m))))).length ≤ weight c
  exact segment_length_le c (φ.obj 0) (φ.obj (Fin.last m))
    (leOfHom (φ.map (homOfLE (Fin.zero_le (Fin.last m)))))

/-- The actual full native nerve subcomplex, with every original simplicial operator. -/
def generatorSpine (V : Type u) [Quiver.{u + 1} V] : (nerve (Paths V)).Subcomplex where
  obj _ := {c | weight c ≤ 1}
  map φ c hc := le_trans (weight_whisker_le c (SimplexCategory.toCat.map φ.unop).toFunctor) hc

theorem mem_generatorSpine_iff {n : ℕ} (c : ComposableArrows (Paths V) n) :
    c ∈ (generatorSpine V).obj (op ⦋n⦌) ↔ weight c ≤ 1 := Iff.rfl

theorem weight_vertex (x : V) : weight (ComposableArrows.mk₀ (show Paths V from x)) = 0 := rfl

theorem weight_edge {x y : V} (f : x ⟶ y) :
    weight (ComposableArrows.mk₁ f.toPath) = 1 := rfl

end
end DaggerNativeFreePathNerveWeight
