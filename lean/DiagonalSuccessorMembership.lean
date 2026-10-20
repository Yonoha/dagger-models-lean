import OriginalDiagonalStages
import DiagonalAttachingData
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-! D5 source implementation only. All ranks and row maps are the original ones.
No declaration in this source packet has been compiled or axiom-audited. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerBisimplicialDiagonal DaggerOriginalDiagonalStages

universe u
namespace DaggerOriginalDiagonalSuccessor
noncomputable section

/-- The actual latching union is precisely outer degeneracy at the supplied inner degree. -/
theorem latching_mem_iff_degenerate (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (y : (B.obj (op ⦋n⦌)).obj q) :
    y ∈ (latching B n).obj q ↔ y ∈ (outerAt B q).degenerate n := by
  cases n with
  | zero => simp [latching, SSet.degenerate_zero]
  | succ n =>
      rw [SSet.degenerate_eq_iUnion_range_σ]
      simp only [latching, Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion]
      rfl

/-- EZ dimension uniqueness bounds every alternative representation of the same simplex. -/
theorem nonDegenerate_dim_le_of_image (X : SSet.{u}) {d n m : ℕ}
    (f : ⦋d⦌ ⟶ ⦋n⦌) [Epi f] (y : X.nonDegenerate n)
    (g : ⦋d⦌ ⟶ ⦋m⦌) (z : X _⦋m⦌)
    (h : X.map f.op y = X.map g.op z) : n ≤ m := by
  obtain ⟨k, e, he, t, ht⟩ :=
    X.exists_nonDegenerate (n := (image g).len) (X.map (image.ι g).op z)
  letI : Epi e := he
  have hrep : X.map f.op y = X.map (factorThruImage g ≫ e).op t := by
    rw [op_comp, FunctorToTypes.map_comp_apply, ← ht,
      ← FunctorToTypes.map_comp_apply, ← op_comp, image.fac]
    exact h
  have hdim := X.unique_nonDegenerate_dim (X.map f.op y) f y rfl
    (factorThruImage g ≫ e) t hrep
  have hk := SimplexCategory.len_le_of_epi e
  have hm := SimplexCategory.len_le_of_mono (image.ι g)
  simpa only [hdim] using hk.trans hm

/-- A nonsurjective simplex map has a genuinely lower-dimensional actual image. -/
theorem image_len_lt_of_not_surjective {d n : ℕ} (f : ⦋d⦌ ⟶ ⦋n⦌)
    (hf : ¬Function.Surjective f.toOrderHom) : (image f).len < n := by
  apply lt_of_le_of_ne (SimplexCategory.len_le_of_mono (image.ι f))
  intro h
  letI : IsIso (image.ι f) := (SimplexCategory.isIso_iff_of_mono _).2 h
  haveI : Epi f := by rw [← image.fac f]; infer_instance
  exact hf (SimplexCategory.epi_iff_surjective.mp inferInstance)

/-- Evaluation of the n-th row always lands in the same stage n+1. -/
theorem rowEval_mem_succ (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ)
    (p : (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q) :
    (rowEval B n).app q p ∈ (stage B (n + 1)).obj q :=
  ⟨n, Nat.lt_succ_self n, SSet.stdSimplex.objEquiv p.2, p.1, rfl⟩

/-- The WHOLE attaching union is the exact preimage of the preceding stage. -/
theorem rowEval_preimage (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ)
    (p : (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q) :
    (rowEval B n).app q p ∈ (stage B n).obj q ↔ p ∈ (attaching B n).obj q := by
  rw [attaching_mem_iff, latching_mem_iff_degenerate]
  let X := outerAt B q
  let f := SSet.stdSimplex.objEquiv p.2
  constructor
  · intro hp
    by_contra h
    have hy : p.1 ∈ X.nonDegenerate n := (not_or.mp h).1
    have hf : Function.Surjective f.toOrderHom := not_not.mp (not_or.mp h).2
    letI : Epi f := SimplexCategory.epi_iff_surjective.mpr hf
    obtain ⟨m, hm, g, z, hz⟩ := hp
    have hn := nonDegenerate_dim_le_of_image (d := q.unop.len) X f ⟨p.1, hy⟩ g z hz.symm
    exact (not_le_of_gt hm) hn
  · rintro (hy | hf)
    · obtain ⟨m, hm, g, z, hz⟩ := hy
      refine ⟨m, hm, f ≫ g, z, ?_⟩
      change X.map (f ≫ g).op z = X.map f.op p.1
      rw [op_comp, FunctorToTypes.map_comp_apply, hz]
    · have hdim := image_len_lt_of_not_surjective (d := q.unop.len) f hf
      refine ⟨(image f).len, hdim, factorThruImage f, X.map (image.ι f).op p.1, ?_⟩
      change X.map (factorThruImage f).op (X.map (image.ι f).op p.1) = X.map f.op p.1
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, image.fac]

/-- The degreewise equivalence is an equality of the original whole subcomplexes. -/
theorem attaching_eq_preimage (B : SimplicialObject SSet.{u}) (n : ℕ) :
    attaching B n = (stage B n).preimage (rowEval B n) := by
  ext q p
  exact (rowEval_preimage B n q p).symm

/-- Both outer nondegeneracy AND surjectivity are retained in the interior. -/
theorem rowEval_interior_injective (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ)
    (p p' : (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q)
    (hp : p ∉ (attaching B n).obj q) (hp' : p' ∉ (attaching B n).obj q)
    (h : (rowEval B n).app q p = (rowEval B n).app q p') : p = p' := by
  rw [attaching_mem_iff, latching_mem_iff_degenerate] at hp hp'
  let X := outerAt B q
  let f := SSet.stdSimplex.objEquiv p.2
  let g := SSet.stdSimplex.objEquiv p'.2
  let y : X.nonDegenerate n := ⟨p.1, (not_or.mp hp).1⟩
  let z : X.nonDegenerate n := ⟨p'.1, (not_or.mp hp').1⟩
  letI : Epi f := SimplexCategory.epi_iff_surjective.mpr (not_not.mp (not_or.mp hp).2)
  have hrep : X.map f.op y = X.map g.op z := h
  have hyz := X.unique_nonDegenerate_simplex (n := q.unop.len) (X.map f.op y) f y rfl g z hrep
  have hfg := X.unique_nonDegenerate_map (n := q.unop.len) (X.map f.op y) f y rfl g z hrep
  exact Prod.ext (congrArg Subtype.val hyz) (SSet.stdSimplex.objEquiv.injective hfg)

/-- The literal two images cover stage n+1; lower witnesses are not discarded. -/
theorem mem_stage_succ_iff (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (x : (DaggerBisimplicialDiagonal.diag B).obj q) :
    x ∈ (stage B (n + 1)).obj q ↔ x ∈ (stage B n).obj q ∨
      ∃ p : (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q, (rowEval B n).app q p = x := by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    obtain hmn | rfl := lt_or_eq_of_le (Nat.lt_succ_iff.mp hm)
    · exact Or.inl ⟨m, hmn, f, y, hy⟩
    · exact Or.inr ⟨(y, SSet.stdSimplex.objEquiv.symm f), by simpa [rowEval] using hy⟩
  · rintro (hx | ⟨p, rfl⟩)
    · exact stage_le_succ B n q hx
    · exact rowEval_mem_succ B n q p

end
end DaggerOriginalDiagonalSuccessor
