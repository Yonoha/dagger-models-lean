import OriginalFullVertexSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Full vertex subcomplexes of Kan complexes

If a simplex is retained precisely when all its vertices belong to a chosen
set, a horn in the retained subcomplex has a filler there. For dimensions at
least two, the horn already contains every vertex. In dimension one, its
single vertex admits a degenerate edge filler.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open SSet.modelCategoryQuillen
open DaggerOriginalFullVertexSubcomplex

universe u

namespace DaggerOriginalFullVertexSubcomplex

noncomputable section

private def liftSimplex {X : SSet.{u}} (V : Set (X.obj (op ⦋0⦌)))
    {n : ℕ} (σ : Δ[n] ⟶ X)
    (hvertex : ∀ w : Δ[n] _⦋0⦌, σ.app (op ⦋0⦌) w ∈ V) :
    Δ[n] ⟶ (fullVertexSubcomplex X V : SSet) :=
  SSet.Subcomplex.lift σ (by
    intro m s hs
    obtain ⟨a, rfl⟩ := hs
    change ∀ v : ⦋0⦌ ⟶ m.unop, X.map v.op (σ.app m a) ∈ V
    intro v
    have hn := congrFun (σ.naturality v.op) a
    change σ.app (op ⦋0⦌) ((Δ[n]).map v.op a) =
      X.map v.op (σ.app m a) at hn
    rw [← hn]
    exact hvertex _)

private theorem hornFillingOne {X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌))) (i : Fin 2)
    (t : (Λ[1, i] : SSet.{u}) ⟶ (fullVertexSubcomplex X V : SSet)) :
    ∃ τ : Δ[1] ⟶ (fullVertexSubcomplex X V : SSet),
      t = Λ[1, i].ι ≫ τ := by
  let j : Fin 2 := if i = 0 then 1 else 0
  have hj : j ≠ i := by fin_cases i <;> decide
  let y : (fullVertexSubcomplex X V : SSet) _⦋0⦌ :=
    t.app (op ⦋0⦌) (SSet.horn.face i j hj)
  refine ⟨SSet.const y, ?_⟩
  apply SSet.horn.hom_ext
  intro k hk
  have hkj : k = j := by fin_cases i <;> fin_cases k <;> simp_all [j]
  subst k
  change t.app (op ⦋0⦌) (SSet.horn.face i j hj) =
    (SSet.const y).app (op ⦋0⦌)
      ((Λ[1, i].ι).app (op ⦋0⦌) (SSet.horn.face i j hj))
  have hid : (⦋0⦌.const ⦋0⦌ 0) = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  simpa only [SSet.const_app, hid, op_id, FunctorToTypes.map_id_apply] using
    (show t.app (op ⦋0⦌) (SSet.horn.face i j hj) = y from rfl)

/-- Any full vertex subcomplex of a Kan complex is again a Kan complex. -/
instance fullVertexSubcomplex_kan {X : SSet.{u}} [SSet.KanComplex X]
    (V : Set (X.obj (op ⦋0⦌))) :
    SSet.KanComplex (fullVertexSubcomplex X V : SSet) := by
  let ambient := X
  change IsFibrant (fullVertexSubcomplex ambient V : SSet)
  rw [isFibrant_iff, fibration_iff]
  intro P Q f hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨i⟩⟩ := hi
  constructor
  intro t _ sq
  let A := fullVertexSubcomplex ambient V
  have hfill : ∃ τ : Δ[n + 1] ⟶ (A : SSet), t = Λ[n + 1, i].ι ≫ τ := by
    cases n with
    | zero =>
        exact hornFillingOne V i t
    | succ n =>
        obtain ⟨σ, hσ⟩ :=
          SSet.KanComplex.hornFilling (t ≫ A.ι)
        have hv : ∀ w : Δ[n + 2] _⦋0⦌, σ.app (op ⦋0⦌) w ∈ V := by
          intro w
          have hw : w ∈ (Λ[n + 2, i]).obj (op ⦋0⦌) := by
            rw [SSet.horn_obj_zero]
            trivial
          let z : (Λ[n + 2, i] : SSet.{u}) _⦋0⦌ := ⟨w, hw⟩
          have hz : (t.app (op ⦋0⦌) z).val ∈ V := by
            have hmem := (t.app (op ⦋0⦌) z).property (𝟙 ⦋0⦌)
            simpa using hmem
          have heq := congrArg
            (fun f : (Λ[n + 2, i] : SSet.{u}) ⟶ ambient => f.app (op ⦋0⦌) z) hσ
          have heq' : (t.app (op ⦋0⦌) z).val = σ.app (op ⦋0⦌) w := by
            simpa only [SSet.comp_app, types_comp_apply] using heq
          exact heq' ▸ hz
        let τ := liftSimplex V σ hv
        refine ⟨τ, ?_⟩
        apply SSet.hom_ext
        intro m
        funext s
        apply Subtype.ext
        have heq := congrArg
          (fun f : (Λ[n + 2, i] : SSet.{u}) ⟶ ambient => f.app m s) hσ
        simpa only [SSet.comp_app, types_comp_apply,
          SSet.Subcomplex.lift_app_coe] using heq
  obtain ⟨τ, hτ⟩ := hfill
  refine CommSq.HasLift.mk' {
    l := τ
    fac_left := hτ.symm
    fac_right := Subsingleton.elim _ _
  }

end

end DaggerOriginalFullVertexSubcomplex
