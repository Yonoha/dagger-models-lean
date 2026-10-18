import PrescribedCollapseFactorization
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
Source-only candidate for the same supplied EZ decomposition. These bodies have not
been type-checked. The imported original rho/finite/factorization are accepted runtime inputs.
-/

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerBisimplicialDiagonal

theorem mem_sigma_range_iff_ez_collapse (X : SSet.{u}) {n m : ℕ}
    (x : X _⦋n + 1⦌) (f : ⦋n + 1⦌ ⟶ ⦋m⦌) [Epi f]
    (y : X.nonDegenerate m) (hxy : x = X.map f.op y) (i : Fin (n + 1)) :
    x ∈ Set.range (X.σ i) ↔ f.toOrderHom i.castSucc = f.toOrderHom i.succ := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨k, g, hg, z, hz⟩ := X.exists_nonDegenerate v
    letI : Epi g := hg
    have hxz : X.σ i v = X.map (SimplexCategory.σ i ≫ g).op z := by
      change X.map (SimplexCategory.σ i).op v = _
      rw [hz, op_comp, FunctorToTypes.map_comp_apply]
    have hdim : m = k :=
      X.unique_nonDegenerate_dim (X.σ i v) f y hxy
        (SimplexCategory.σ i ≫ g) z hxz
    subst k
    have hf : f = SimplexCategory.σ i ≫ g :=
      X.unique_nonDegenerate_map (X.σ i v) f y hxy
        (SimplexCategory.σ i ≫ g) z hxz
    rw [hf]
    change g.toOrderHom (i.predAbove i.castSucc) = g.toOrderHom (i.predAbove i.succ)
    simp only [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  · intro hi
    obtain ⟨g, hg⟩ := SimplexCategory.eq_σ_comp_of_not_injective' f i hi
    refine ⟨X.map g.op y, ?_⟩
    change X.map (SimplexCategory.σ i).op (X.map g.op y) = x
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← hg]
    exact hxy.symm

theorem mem_rho_range_iff_ez_collapses (X : SSet.{u}) {n m : ℕ}
    (I : Finset (Fin n)) (x : X _⦋n⦌) (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    (y : X.nonDegenerate m) (hxy : x = X.map f.op y) :
    x ∈ Set.range (X.map (rho I).op) ↔
      ∀ i ∈ I, f.toOrderHom i.castSucc = f.toOrderHom i.succ := by
  constructor
  · intro hx
    cases n with
    | zero =>
        intro i _
        exact Fin.elim0 i
    | succ n =>
        intro i hi
        apply (mem_sigma_range_iff_ez_collapse X x f y hxy i).mp
        obtain ⟨z, hz⟩ := hx
        obtain ⟨g, hg⟩ := SimplexCategory.eq_σ_comp_of_not_injective'
          (rho I) i ((rho_adjacent_iff I i).mpr hi)
        refine ⟨X.map g.op z, ?_⟩
        change X.map (SimplexCategory.σ i).op (X.map g.op z) = x
        rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← hg]
        exact hz
  · intro hf
    refine ⟨X.map (rhoFactor I f).op y, ?_⟩
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, rhoFactor_fac I f hf]
    exact hxy.symm

end DaggerBisimplicialDiagonal
