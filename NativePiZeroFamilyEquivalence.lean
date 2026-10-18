import NativeFamilyWeak
import OriginalSimplicialPiZeroCategory

/-! The original component quotient of a simplicial family is its full component family. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerOriginalProductGadget DaggerNativeFamilyWeak
universe u
namespace DaggerNativePiZeroFamilyEquivalence
noncomputable section

def familyComponents (J : Type u) (X : J → SSet.{u}) : (familySSet X).π₀ → Σ j, (X j).π₀ :=
  Quot.lift (fun a ↦ ⟨a.1, SSet.π₀.mk a.2⟩) (by
    rintro a b ⟨s, ha, hb⟩
    rw [← ha, ← hb]
    rcases s with ⟨j, e⟩
    exact Sigma.ext rfl (heq_of_eq (SSet.π₀.sound e rfl rfl)))

def familyComponentsEquiv (J : Type u) (X : J → SSet.{u}) :
    (familySSet X).π₀ ≃ Σ j, (X j).π₀ where
  toFun := familyComponents J X
  invFun q := SSet.mapπ₀ (familyInclusion X q.1) q.2
  left_inv q := by
    obtain ⟨⟨j, a⟩, rfl⟩ := SSet.π₀.mk_surjective q
    rfl
  right_inv q := by
    obtain ⟨j, a⟩ := q
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
    rfl

theorem familyComponentsEquiv_mk {J : Type u} (X : J → SSet.{u}) (j : J)
    (a : (X j) _⦋0⦌) :
    familyComponentsEquiv J X (SSet.π₀.mk ⟨j, a⟩) = ⟨j, SSet.π₀.mk a⟩ := rfl

theorem familyComponentsEquiv_natural {J : Type u} {X Y : J → SSet.{u}}
    (f : ∀ j, X j ⟶ Y j) (q : (familySSet X).π₀) :
    familyComponentsEquiv J Y (SSet.mapπ₀ (familyMap f) q) =
      ⟨(familyComponentsEquiv J X q).1,
        SSet.mapπ₀ (f (familyComponentsEquiv J X q).1) (familyComponentsEquiv J X q).2⟩ := by
  obtain ⟨⟨j, a⟩, rfl⟩ := SSet.π₀.mk_surjective q
  rfl

end
end DaggerNativePiZeroFamilyEquivalence
