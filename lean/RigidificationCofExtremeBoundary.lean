import RigidificationCofFiniteFacets

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

abbrev interior (n : ℕ) := {k : Fin (n + 2) // 0 < k ∧ k < Fin.last (n + 1)}

abbrev extremeHom (n : ℕ) : SSet.{u} :=
  hom (ULift.up (0 : Fin (n + 2))) (ULift.up (Fin.last (n + 1)))

def extremeOmitted (n : ℕ) (k : interior n) : (extremeHom.{u} n).Subcomplex :=
  omitted (ULift.up 0) (ULift.up (Fin.last (n + 1))) (ULift.up k.val)

def extremeCut (n : ℕ) (k : interior n) : (extremeHom.{u} n).Subcomplex :=
  cut (ULift.up 0) (ULift.up (Fin.last (n + 1))) (ULift.up k.val)

/-- The ENTIRE original omitted/cut union, with one common position along each chain. -/
noncomputable def extremeBoundary (n : ℕ) : (extremeHom.{u} n).Subcomplex :=
  ⨆ k : interior n, extremeOmitted n k ⊔ extremeCut n k

theorem mem_extremeBoundary (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (γ : (extremeHom.{u} n).obj q) :
    γ ∈ (extremeBoundary n).obj q ↔
      ∃ k : interior n,
        (∀ t, ULift.up k.val ∉ (γ.obj t).I) ∨
        (∀ t, ULift.up k.val ∈ (γ.obj t).I) := by
  simp only [extremeBoundary, Subfunctor.iSup_obj, Set.mem_iUnion]
  rfl

theorem omitted_le_extremeBoundary (n : ℕ) (k : interior n) :
    extremeOmitted.{u} n k ≤ extremeBoundary n := by
  unfold extremeBoundary
  exact le_trans le_sup_left (le_iSup (fun l => extremeOmitted n l ⊔ extremeCut n l) k)

theorem cut_le_extremeBoundary (n : ℕ) (k : interior n) :
    extremeCut.{u} n k ≤ extremeBoundary n := by
  unfold extremeBoundary
  exact le_trans le_sup_right (le_iSup (fun l => extremeOmitted n l ⊔ extremeCut n l) k)

instance interior_zero_empty : IsEmpty (interior 0) := ⟨fun k => by
  have h₀ : 1 ≤ k.val.val := k.property.1
  have h₁ : k.val.val < 1 := k.property.2
  exact (not_lt_of_ge h₀) h₁⟩

theorem extremeBoundary_zero : extremeBoundary.{u} 0 = ⊥ := by
  apply le_antisymm
  · intro q γ h
    obtain ⟨k, _⟩ := (mem_extremeBoundary 0 q γ).mp h
    exact isEmptyElim k
  · exact bot_le

theorem mem_extreme_oo_overlap (n : ℕ) (k l : interior n)
    (q : SimplexCategoryᵒᵖ) (γ : (extremeHom.{u} n).obj q) :
    γ ∈ (extremeOmitted n k ⊓ extremeOmitted n l).obj q ↔
      (∀ t, ULift.up k.val ∉ (γ.obj t).I) ∧
      (∀ t, ULift.up l.val ∉ (γ.obj t).I) := Iff.rfl

theorem mem_extreme_kk_overlap (n : ℕ) (k l : interior n)
    (q : SimplexCategoryᵒᵖ) (γ : (extremeHom.{u} n).obj q) :
    γ ∈ (extremeCut n k ⊓ extremeCut n l).obj q ↔
      (∀ t, ULift.up k.val ∈ (γ.obj t).I) ∧
      (∀ t, ULift.up l.val ∈ (γ.obj t).I) := Iff.rfl

theorem mem_extreme_ok_overlap (n : ℕ) (k l : interior n)
    (q : SimplexCategoryᵒᵖ) (γ : (extremeHom.{u} n).obj q) :
    γ ∈ (extremeOmitted n k ⊓ extremeCut n l).obj q ↔
      (∀ t, ULift.up k.val ∉ (γ.obj t).I) ∧
      (∀ t, ULift.up l.val ∈ (γ.obj t).I) := Iff.rfl

theorem extreme_same_disjoint (n : ℕ) (k : interior n) :
    extremeOmitted.{u} n k ⊓ extremeCut n k = ⊥ := omitted_cut_disjoint _ _ _

end DaggerOrdinaryRigidificationCof.PathFacets
