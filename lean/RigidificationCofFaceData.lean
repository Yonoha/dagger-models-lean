import RigidificationCofBase
import RigidificationCofFiniteFacets

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open DaggerModels.OrdinaryRigidification.NerveVertices

def vertexMap {n : ℕ} (i : Fin (n + 1)) : ⦋0⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom (OrderHom.const _ i)

theorem vertexMap_comp {n : ℕ} {m : SimplexCategory} (φ : m ⟶ ⦋n⦌)
    (i : Fin (m.len + 1)) : vertexMap i ≫ φ = vertexMap (φ.toOrderHom i) := by
  ext t
  rfl

theorem vertexMap_not_surjective {n : ℕ} (i : Fin (n + 2)) :
    ¬ Function.Surjective (vertexMap i).toOrderHom := by
  obtain ⟨j, hj⟩ := exists_ne i
  intro h
  obtain ⟨k, hk⟩ := h j
  exact hj hk.symm

variable {A B : SC.{u}} {n : ℕ}

theorem simplex_eq {d : SimplexCategory}
    (a : (SSet.boundary d.len).toSSet ⟶ N.obj A)
    {m : SimplexCategory} {φ ψ : m ⟶ d}
    (e : φ = ψ) (hφ : ¬ Function.Surjective φ.toOrderHom)
    (hψ : ¬ Function.Surjective ψ.toOrderHom) :
    simplex (n := d) a φ hφ = simplex (n := d) a ψ hψ := by
  cases e
  rfl

/-- The object is evaluated from the SAME supplied boundary vertex, without a face choice. -/
def vertex (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A) (i : Fin (n + 2)) : A.Obj :=
  (simplex (n := ⦋n + 1⦌) a (vertexMap i) (vertexMap_not_surjective i)).obj zeroObject

theorem simplex_obj (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    {m : SimplexCategory} (φ : m ⟶ ⦋n + 1⦌)
    (hφ : ¬ Function.Surjective φ.toOrderHom) (i : Fin (m.len + 1)) :
    (simplex (n := ⦋n + 1⦌) a φ hφ).obj (.mk (ULift.up i)) = vertex a (φ.toOrderHom i) := by
  have h := congrArg (fun F : T.obj ⦋0⦌ ⟶ A => F.obj zeroObject)
    (simplex_precompose (n := ⦋n + 1⦌) a φ hφ (vertexMap i))
  exact h.trans (congrArg (fun F : T.obj ⦋0⦌ ⟶ A => F.obj zeroObject)
    (simplex_eq (d := ⦋n + 1⦌) a (vertexMap_comp φ i) _ (vertexMap_not_surjective _)))

theorem vertex_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b) (i : Fin (n + 2)) :
    p.obj (vertex a i) = (top b).obj (.mk (ULift.up i)) :=
  congrArg (fun F : T.obj ⦋0⦌ ⟶ B => F.obj zeroObject)
    (simplex_over (n := ⦋n + 1⦌) a b p sq (vertexMap i) (vertexMap_not_surjective i))

theorem delta_not_surjective (k : Fin (n + 2)) :
    ¬ Function.Surjective (SimplexCategory.δ k).toOrderHom := by
  intro h
  obtain ⟨i, hi⟩ := h k
  exact Fin.succAbove_ne k i hi

/-- Every original codimension-one face retains its whole enriched functor. -/
def facet (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A) (k : Fin (n + 2)) :
    T.obj ⦋n⦌ ⟶ A :=
  simplex (n := ⦋n + 1⦌) a (SimplexCategory.δ k) (delta_not_surjective k)

theorem facet_obj (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k : Fin (n + 2)) (i : Fin (n + 1)) :
    (facet a k).obj (.mk (ULift.up i)) = vertex a (k.succAbove i) :=
  simplex_obj a (SimplexCategory.δ k) (delta_not_surjective k) i

theorem facet_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b) (k : Fin (n + 2)) :
    facet a k ≫ p = T.map (SimplexCategory.δ k) ≫ top b :=
  simplex_over (n := ⦋n + 1⦌) a b p sq (SimplexCategory.δ k) (delta_not_surjective k)

end

end DaggerOrdinaryRigidificationCof.BoundaryData
