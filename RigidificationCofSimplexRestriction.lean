import RigidificationCofOver

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}} {m : SimplexCategory}

def faceLift (s : Finset (Fin (n + 1))) (φ : m ⟶ ⦋n⦌)
    (hφ : ∀ i, φ.toOrderHom i ∈ s) : Fin (m.len + 1) →o s where
  toFun i := ⟨φ.toOrderHom i, hφ i⟩
  monotone' _ _ h := φ.toOrderHom.monotone h

def factorOrdinal (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (φ : m ⟶ ⦋n⦌) (hφ : ∀ i, φ.toOrderHom i ∈ s) : m ⟶ ⦋faceDimension s⦌ :=
  SimplexCategory.mkHom ((faceBackward s hs).comp (faceLift s φ hφ))

theorem factorOrdinal_comp (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (φ : m ⟶ ⦋n⦌) (hφ : ∀ i, φ.toOrderHom i ∈ s) :
    factorOrdinal s hs φ hφ ≫ faceOrdinal s hs = φ := by
  ext i
  change (((faceOrderIso s hs) ((faceOrderIso s hs).symm _)).val).val = _
  simp only [OrderIso.apply_symm_apply]
  rfl

/-- Every actual proper simplex restricts from the SAME original boundary map. -/
theorem simplex_from_face (a : (SSet.boundary n).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (φ : m ⟶ ⦋n⦌) (hφ : ∀ i, φ.toOrderHom i ∈ s)
    (hn : ¬ Function.Surjective φ.toOrderHom) :
    SimplicialThickening.functor (faceLift s φ hφ).uliftMap ≫
      faceFunctor a s hs hp = simplex (n := ⦋n⦌) a φ hn := by
  have h := (simplex_precompose (n := ⦋n⦌) a (faceOrdinal s hs)
    (faceOrdinal_not_surjective s hs hp) (factorOrdinal s hs φ hφ)).trans
      (simplex_eq (d := ⦋n⦌) a (factorOrdinal_comp s hs φ hφ) _ hn)
  unfold faceFunctor
  rw [← Category.assoc]
  change EnrichedFunctor.comp SSet
    (EnrichedFunctor.comp SSet (SimplicialThickening.functor (faceLift s φ hφ).uliftMap)
      (SimplicialThickening.functor (faceBackward s hs).uliftMap)) _ = _
  rw [← SimplicialThickening.functor_comp]
  exact h

/-- The original simplex functor, with its object names literally the boundary vertices. -/
def canonicalSimplex (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (φ : m ⟶ ⦋n + 1⦌) (hn : ¬ Function.Surjective φ.toOrderHom) : T.obj m ⟶ A :=
  reobject (simplex (n := ⦋n + 1⦌) a φ hn)
    (fun x => vertex a (φ.toOrderHom x.as.down))
    (fun x => simplex_obj a φ hn x.as.down)

theorem canonicalSimplex_eq (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (φ : m ⟶ ⦋n + 1⦌) (hn : ¬ Function.Surjective φ.toOrderHom) :
    canonicalSimplex a φ hn = simplex (n := ⦋n + 1⦌) a φ hn := reobject_self _ _ _

theorem canonicalSimplex_from_face (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (φ : m ⟶ ⦋n + 1⦌) (hφ : ∀ i, φ.toOrderHom i ∈ s)
    (hn : ¬ Function.Surjective φ.toOrderHom) :
    SimplicialThickening.functor (faceLift s φ hφ).uliftMap ≫
      canonicalFaceFunctor a s hs hp = canonicalSimplex a φ hn := by
  rw [canonicalFaceFunctor_eq, canonicalSimplex_eq]
  exact simplex_from_face a s hs hp φ hφ hn

end

end DaggerOrdinaryRigidificationCof.BoundaryData
