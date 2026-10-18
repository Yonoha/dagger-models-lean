import NativeNerveFrontDegeneracy

/-! Adjoining an arrow preserves degeneracy of the tail of a native nerve simplex. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeNerveFrontDegeneracy
universe u v
namespace DaggerNativeNerveTailDegeneracy

variable {C : Type u} [Category.{v} C]

theorem precomp_degenerate_of_tail {n : ℕ} (c : ComposableArrows C n) {X : C}
    (f : X ⟶ c.left) (hc : c ∈ (nerve C).degenerate n) :
    c.precomp f ∈ (nerve C).degenerate (n + 1) := by
  cases n with
  | zero => simp at hc
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion] at hc
    obtain ⟨i, z, rfl⟩ := hc
    have he := sigma_succ_precomp z (f ≫ eqToHom (sigma_left z i)) i
    have he' : (nerve C).σ i.succ (z.precomp (f ≫ eqToHom (sigma_left z i))) =
        ((nerve C).σ i z).precomp f := by simpa using he
    rw [← he']
    exact SSet.σ_mem_degenerate _ _ _

theorem tail_nonDegenerate {n : ℕ} (c : ComposableArrows C n) {X : C}
    (f : X ⟶ c.left) (hc : c.precomp f ∈ (nerve C).nonDegenerate (n + 1)) :
    c ∈ (nerve C).nonDegenerate n := by
  change c ∉ (nerve C).degenerate n
  exact fun hd ↦ hc (precomp_degenerate_of_tail c f hd)

end DaggerNativeNerveTailDegeneracy
