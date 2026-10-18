import RigidificationCofSubsets

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.SubcomplexNerveData

noncomputable section

open DaggerOrdinaryRigidificationCof.BoundaryData

variable {d : ℕ} (K : (Δ[d] : SSet.{u}).Subcomplex) {A : SC.{u}}

/-- Membership of the exact ordinal simplex in the supplied subcomplex. -/
def Contains {m : SimplexCategory} (φ : m ⟶ ⦋d⦌) : Prop :=
  SSet.stdSimplex.objEquiv.symm φ ∈ K.obj (op m)

/-- A simplex of `K` stays in `K` under every original simplex operator. -/
theorem contains_comp {m l : SimplexCategory} (φ : m ⟶ ⦋d⦌)
    (hφ : Contains K φ) (ψ : l ⟶ m) : Contains K (ψ ≫ φ) := by
  have h := K.map ψ.op hφ
  exact h

/-- Evaluate an included simplex as the original full enriched functor. -/
def simplex (a : (K : SSet) ⟶ N.obj A) {m : SimplexCategory}
    (φ : m ⟶ ⦋d⦌) (hφ : Contains K φ) : T.obj m ⟶ A :=
  (a.app (op m) ⟨SSet.stdSimplex.objEquiv.symm φ, hφ⟩).down

/-- Membership witnesses do not affect the actual evaluated functor. -/
theorem simplex_eq (a : (K : SSet) ⟶ N.obj A)
    {m : SimplexCategory} {φ ψ : m ⟶ ⦋d⦌}
    (e : φ = ψ) (hφ : Contains K φ) (hψ : Contains K ψ) :
    simplex K a φ hφ = simplex K a ψ hψ := by
  cases e
  rfl

/-- Full enriched evaluation respects precomposition by the original operator. -/
theorem simplex_precompose (a : (K : SSet) ⟶ N.obj A)
    {m l : SimplexCategory} (φ : m ⟶ ⦋d⦌) (hφ : Contains K φ)
    (ψ : l ⟶ m) :
    T.map ψ ≫ simplex K a φ hφ =
      simplex K a (ψ ≫ φ) (contains_comp K φ hφ ψ) := by
  have h := congrFun (a.naturality ψ.op)
    ⟨SSet.stdSimplex.objEquiv.symm φ, hφ⟩
  exact (congrArg ULift.down h).symm

/-- Evaluate a finite nonempty face only when that face actually lies in `K`. -/
def faceFunctor (a : (K : SSet) ⟶ N.obj A)
    (s : Finset (Fin (d + 1))) (hs : s.Nonempty)
    (hface : Contains K (faceOrdinal s hs)) :
    DaggerModels.SimplicialCat.of (SimplicialThickening (ULift.{u} s)) ⟶ A :=
  SimplicialThickening.functor (faceBackward s hs).uliftMap ≫
    simplex K a (faceOrdinal s hs) hface

/-- Restriction is equality of whole original enriched functors and all Hom simplices. -/
theorem faceFunctor_restrict (a : (K : SSet) ⟶ N.obj A)
    (s t : Finset (Fin (d + 1))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hfs : Contains K (faceOrdinal s hs))
    (hft : Contains K (faceOrdinal t ht)) (hst : s ⊆ t) :
    SimplicialThickening.functor (faceInclusion hst).uliftMap ≫
      faceFunctor K a t ht hft = faceFunctor K a s hs hfs := by
  let hcomp := contains_comp K (faceOrdinal t ht) hft
    (restrictionOrdinal s t hs ht hst)
  have h₀ := simplex_precompose K a (faceOrdinal t ht) hft
    (restrictionOrdinal s t hs ht hst)
  have h₁ := simplex_eq K a (restrictionOrdinal_comp s t hs ht hst) hcomp hfs
  have h := h₀.trans h₁
  unfold faceFunctor
  rw [← Category.assoc, ← h, ← Category.assoc]
  congr 1
  change EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (faceInclusion hst).uliftMap)
      (SimplicialThickening.functor (faceBackward t ht).uliftMap) =
    EnrichedFunctor.comp SSet
      (SimplicialThickening.functor (faceBackward s hs).uliftMap)
      (SimplicialThickening.functor
        (restrictionOrdinal s t hs ht hst).toOrderHom.uliftMap)
  rw [← SimplicialThickening.functor_comp, ← SimplicialThickening.functor_comp]
  congr 1
  apply DFunLike.ext
  intro i
  apply ULift.ext
  change (faceOrderIso t ht).symm ((faceInclusion hst) i.down) =
    (faceOrderIso t ht).symm ((faceInclusion hst)
      ((faceOrderIso s hs) ((faceOrderIso s hs).symm i.down)))
  simp only [OrderIso.apply_symm_apply]

end

end DaggerOrdinaryRigidificationCof.SubcomplexNerveData
