import PrescribedCollapseFinite
import Mathlib.CategoryTheory.EpiMono
import Mathlib.Data.Fin.SuccPred

/-!
SOURCE-ONLY proof candidate. No body here has been compiled.
The original rho and finite prerequisites are unchanged source-only accepted inputs.
No Epi f assumption or new epimorphism constructor is introduced.
-/

open CategoryTheory Simplicial

namespace DaggerBisimplicialDiagonal

theorem rho_fiber_const {n m : ℕ} (I : Finset (Fin n)) (f : ⦋n⦌ ⟶ ⦋m⦌)
    (hf : ∀ i ∈ I, f.toOrderHom i.castSucc = f.toOrderHom i.succ)
    (a b : Fin (n + 1))
    (hab : (rho I).toOrderHom a = (rho I).toOrderHom b) :
    f.toOrderHom a = f.toOrderHom b := by
  have ordered : ∀ (b a : Fin (n + 1)), a ≤ b →
      (rho I).toOrderHom a = (rho I).toOrderHom b →
      f.toOrderHom a = f.toOrderHom b := by
    intro b
    induction b using Fin.induction with
    | zero =>
      intro a ha _
      have ha0 : a = 0 := le_antisymm ha (Fin.zero_le a)
      subst a
      rfl
    | succ b ih =>
      intro a ha hr
      by_cases heq : a = b.succ
      · rw [heq]
      · have hp : a ≤ b.castSucc := Fin.le_castSucc_iff.mpr (lt_of_le_of_ne ha heq)
        have hrp : (rho I).toOrderHom a = (rho I).toOrderHom b.castSucc := by
          apply le_antisymm ((rho I).toOrderHom.monotone hp)
          calc
            (rho I).toOrderHom b.castSucc ≤ (rho I).toOrderHom b.succ :=
              (rho I).toOrderHom.monotone (Fin.castSucc_le_succ b)
            _ = (rho I).toOrderHom a := hr.symm
        have hbI : b ∈ I := (rho_adjacent_iff I b).mp (hrp.symm.trans hr)
        calc
          f.toOrderHom a = f.toOrderHom b.castSucc := ih a hp hrp
          _ = f.toOrderHom b.succ := hf b hbI
  rcases le_total a b with h | h
  · exact ordered b a h hab
  · exact (ordered a b h hab.symm).symm

noncomputable def rhoFactor {n m : ℕ} (I : Finset (Fin n)) (f : ⦋n⦌ ⟶ ⦋m⦌) :
    ⦋n - I.card⦌ ⟶ ⦋m⦌ :=
  letI := rho_isSplitEpi I
  section_ (rho I) ≫ f

theorem rhoFactor_fac {n m : ℕ} (I : Finset (Fin n)) (f : ⦋n⦌ ⟶ ⦋m⦌)
    (hf : ∀ i ∈ I, f.toOrderHom i.castSucc = f.toOrderHom i.succ) :
    rho I ≫ rhoFactor I f = f := by
  letI := rho_isSplitEpi I
  ext t : 3
  change f.toOrderHom ((section_ (rho I)).toOrderHom ((rho I).toOrderHom t)) =
    f.toOrderHom t
  apply rho_fiber_const I f hf
  exact SimplexCategory.congr_toOrderHom_apply (IsSplitEpi.id (rho I))
    ((rho I).toOrderHom t)

theorem rho_factorization_iff {n m : ℕ} (I : Finset (Fin n)) (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (∃ g : ⦋n - I.card⦌ ⟶ ⦋m⦌, rho I ≫ g = f) ↔
      ∀ i ∈ I, f.toOrderHom i.castSucc = f.toOrderHom i.succ := by
  constructor
  · rintro ⟨g, hg⟩ i hi
    rw [← hg]
    change g.toOrderHom ((rho I).toOrderHom i.castSucc) =
      g.toOrderHom ((rho I).toOrderHom i.succ)
    exact congrArg g.toOrderHom ((rho_adjacent_iff I i).mpr hi)
  · intro hf
    exact ⟨rhoFactor I f, rhoFactor_fac I f hf⟩

theorem rho_factorization_unique {n m : ℕ} (I : Finset (Fin n))
    {g₁ g₂ : ⦋n - I.card⦌ ⟶ ⦋m⦌} (h : rho I ≫ g₁ = rho I ≫ g₂) : g₁ = g₂ := by
  letI := rho_isSplitEpi I
  exact (cancel_epi (rho I)).mp h

end DaggerBisimplicialDiagonal
