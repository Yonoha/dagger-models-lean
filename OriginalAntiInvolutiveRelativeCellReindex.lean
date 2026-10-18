import OriginalAntiInvolutiveRelativeCellAttachment
import OriginalAntiInvolutiveSimplexReversal

/-!
# Orbit and parameter reindexing for relative anti-involutive cells

The two tags of each genuine new-cell orbit correspond to the two ordinary
new nondegenerate simplices. On the true tag the standard-simplex parameter
must also be reversed. These are actual pointwise equivalences, including in
degree zero, needed to transfer the checked ordinary attachment pushout.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveRelativeCellReindex

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.OriginalAntiInvolutiveNormalGenerators
open DaggerModels.OriginalAntiInvolutiveRelativeCellAttachment
open DaggerModels.OriginalAntiInvolutiveSimplexReversal
open DaggerModels.SSetBoundaryCells

noncomputable section

variable {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) (hf : NormalMono f)

/-- Orbit plus tag is exactly the set of ordinary relative new cells. -/
def orbitTagCellEquiv (n : ℕ) :
    NewCellOrbit f n × Bool ≃ Cells f.hom n :=
  (newCellSplit hf n).symm

/-- Reversal of a standard-simplex parameter is involutive. -/
theorem simplexRevRev (n : ℕ) (k : SimplexCategoryᵒᵖ)
    (a : (Δ[n] : SSet.{u}).obj k) :
    simplexRevEquiv n k (simplexRevEquiv n k a) = a := by
  apply SSet.stdSimplex.objEquiv.injective
  simp [simplexRevEquiv, homRevEquiv]

/-- At each simplicial degree, the actual free orbit-indexed cells are in
bijection with all ordinary relative cells. The true tag reverses its simplex
parameter, which is necessary for naturality. -/
def fullCellEquiv (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    (cellSource f n).toSSet.obj k ≃
      (copies (Cells f.hom n) (Δ[n] : SSet.{u})).obj k where
  toFun p :=
    ⟨orbitTagCellEquiv f hf n (p.1.1, p.2),
      if p.2 then simplexRevEquiv n k p.1.2 else p.1.2⟩
  invFun q :=
    let t := (orbitTagCellEquiv f hf n).symm q.1
    (⟨t.1, if t.2 then simplexRevEquiv n k q.2 else q.2⟩, t.2)
  left_inv p := by
    rcases p with ⟨⟨r, a⟩, b⟩
    cases b <;> simp [orbitTagCellEquiv, simplexRevRev]
  right_inv q := by
    rcases q with ⟨σ, a⟩
    generalize ht : (orbitTagCellEquiv f hf n).symm σ = t
    rcases t with ⟨r, b⟩
    have hs : orbitTagCellEquiv f hf n (r, b) = σ := by
      have h := (orbitTagCellEquiv f hf n).apply_symm_apply σ
      rw [ht] at h
      exact h
    dsimp only
    rw [ht]
    cases b
    · simp [hs]
    · simp [hs, simplexRevRev]

/-- The same bijection restricts to the literal boundaries because reversal
preserves non-surjectivity of simplex operators. -/
def boundaryCellEquiv (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    (boundarySource f n).toSSet.obj k ≃
      (copies (Cells f.hom n) (SSet.boundary.{u} n).toSSet).obj k where
  toFun p :=
    ⟨orbitTagCellEquiv f hf n (p.1.1, p.2),
      ⟨if p.2 then simplexRevEquiv n k p.1.2.1 else p.1.2.1,
        by
          cases hb : p.2
          · simp [p.1.2.2]
          · exact (simplexRev_mem_boundary_iff n k p.1.2.1).2 p.1.2.2⟩⟩
  invFun q :=
    let t := (orbitTagCellEquiv f hf n).symm q.1
    (⟨t.1,
      ⟨if t.2 then simplexRevEquiv n k q.2.1 else q.2.1,
        by
          cases hb : t.2
          · simp [q.2.2]
          · exact (simplexRev_mem_boundary_iff n k q.2.1).2 q.2.2⟩⟩, t.2)
  left_inv p := by
    rcases p with ⟨⟨r, ⟨a, ha⟩⟩, b⟩
    cases b <;> simp [orbitTagCellEquiv, simplexRevRev]
  right_inv q := by
    rcases q with ⟨σ, ⟨a, ha⟩⟩
    generalize ht : (orbitTagCellEquiv f hf n).symm σ = t
    rcases t with ⟨r, b⟩
    have hs : orbitTagCellEquiv f hf n (r, b) = σ := by
      have h := (orbitTagCellEquiv f hf n).apply_symm_apply σ
      rw [ht] at h
      exact h
    dsimp only
    rw [ht]
    cases b
    · simp [hs]
    · simp [hs, simplexRevRev]

end

end DaggerModels.OriginalAntiInvolutiveRelativeCellReindex
