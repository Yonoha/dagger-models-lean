import NativePartialFaceUnionGeometry
import NativeSimplexConeHomotopies
import NativeSubcomplexHomotopyRestriction
import NativeRawHomotopyWeakInvariance

/-! Every proper nonempty union of original simplex faces has weak native inclusion. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Simplicial Opposite
open DaggerNativePartialFaceUnionGeometry DaggerNativeSimplexConeHomotopies
open DaggerNativeSubcomplexHomotopyRestriction DaggerNativeRawHomotopyWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePartialFaceUnionContraction
noncomputable section

variable {n : ℕ} (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) (hk : k ∉ S)
include hk

theorem vertex_mem_faceUnion (hS : S.Nonempty) :
    vertex.{u} n k ∈ (faceUnion S).obj (op ⦋0⦌) := by
  obtain ⟨j, hj⟩ := hS
  refine (mem_faceUnion S _ _).mpr ⟨j, hj, ?_⟩
  intro r
  change k ≠ j
  rintro rfl
  exact hk hj

theorem identityHomotopy_stays (d : SimplexCategoryᵒᵖ)
    (s : (faceUnion.{u} S).obj d) (t : (Δ[1] : SSet.{u}).obj d) :
    (identityHomotopy n k).h.app d (s.val, t) ∈ (faceUnion S).obj d := by
  obtain ⟨j, hj, hx⟩ := (mem_faceUnion S d s.val).mp s.property
  have hkj : k ≠ j := by rintro rfl; exact hk hj
  refine (mem_faceUnion S d _).mpr ⟨j, hj, ?_⟩
  intro r
  have hm : min k (SSet.stdSimplex.asOrderHom s.val r) ≠ j := by
    by_cases h : k ≤ SSet.stdSimplex.asOrderHom s.val r
    · rw [min_eq_left h]
      exact hkj
    · rw [min_eq_right (le_of_not_ge h)]
      exact hx r
  rw [identityHomotopy_vertex]
  split_ifs
  · exact hm
  · exact hx r

theorem constantHomotopy_stays (d : SimplexCategoryᵒᵖ)
    (s : (faceUnion.{u} S).obj d) (t : (Δ[1] : SSet.{u}).obj d) :
    (constantHomotopy n k).h.app d (s.val, t) ∈ (faceUnion S).obj d := by
  obtain ⟨j, hj, hx⟩ := (mem_faceUnion S d s.val).mp s.property
  have hkj : k ≠ j := by rintro rfl; exact hk hj
  refine (mem_faceUnion S d _).mpr ⟨j, hj, ?_⟩
  intro r
  have hm : min k (SSet.stdSimplex.asOrderHom s.val r) ≠ j := by
    by_cases h : k ≤ SSet.stdSimplex.asOrderHom s.val r
    · rw [min_eq_left h]
      exact hkj
    · rw [min_eq_right (le_of_not_ge h)]
      exact hx r
  rw [constantHomotopy_vertex]
  split_ifs
  · exact hm
  · exact hkj

theorem minimum_range : SSet.Subcomplex.range ((faceUnion.{u} S).ι ≫ minimumMap n k) ≤
    faceUnion S := by
  intro d y hy
  obtain ⟨x, rfl⟩ := hy
  let t := ((SSet.ι₀ (X := (faceUnion S : SSet.{u}))).app d x).2
  have hh := identityHomotopy_stays S k hk d x t
  have he : (identityHomotopy n k).h.app d (x.val, t) =
      (minimumMap n k).app d x.val :=
    congrFun (NatTrans.congr_app (identityHomotopy n k).h₀ d) x.val
  exact he ▸ hh

def minimumRestriction : (faceUnion.{u} S : SSet.{u}) ⟶ faceUnion S :=
  SSet.Subcomplex.lift ((faceUnion S).ι ≫ minimumMap n k) (minimum_range S k hk)

def restrictedIdentityHomotopy :
    SSet.Homotopy (minimumRestriction.{u} S k hk) (𝟙 _) :=
  restrictHomotopy (faceUnion S) (identityHomotopy n k)
    (identityHomotopy_stays S k hk) rfl (by simp)

def chosenVertex (hS : S.Nonempty) : (faceUnion.{u} S : SSet.{u}) _⦋0⦌ :=
  ⟨vertex n k, vertex_mem_faceUnion S k hk hS⟩

def restrictedConstantHomotopy (hS : S.Nonempty) :
    SSet.Homotopy (minimumRestriction.{u} S k hk) (SSet.const (chosenVertex S k hk hS)) :=
  restrictHomotopy (faceUnion S) (constantHomotopy n k)
    (constantHomotopy_stays S k hk) rfl (by rw [SSet.const_comp, SSet.comp_const]; rfl)

theorem constant_weak (hS : S.Nonempty) :
    WeakEquivalence (SSet.const (chosenVertex.{u} S k hk hS) :
      (faceUnion S : SSet.{u}) ⟶ faceUnion S) := by
  have hm : WeakEquivalence (minimumRestriction.{u} S k hk) :=
    (weakEquivalence_iff_homotopy (restrictedIdentityHomotopy S k hk)).mpr inferInstance
  exact (weakEquivalence_iff_homotopy (restrictedConstantHomotopy S k hk hS)).mp hm

theorem inclusion_weak (hS : S.Nonempty) : WeakEquivalence (faceUnion.{u} S).ι := by
  let q := SSet.const (DaggerNativeStandardSimplexContraction.firstVertex.{u} 0)
    (X := (Δ[n] : SSet.{u}))
  have hconst : WeakEquivalence
      (SSet.const (DaggerNativeStandardSimplexContraction.firstVertex.{u} n) :
        (Δ[n] : SSet.{u}) ⟶ Δ[n]) :=
    (weakEquivalence_iff_homotopy
      (DaggerNativeStandardSimplexContraction.simplexContractible n).h).mpr inferInstance
  have : WeakEquivalence q := collapse_weak_of_const_weak _ hconst
  have : WeakEquivalence ((faceUnion.{u} S).ι ≫ q) := by
    rw [SSet.comp_const]
    exact collapse_weak_of_const_weak _ (constant_weak S k hk hS)
  exact weakEquivalence_of_postcomp_of_fac (f := (faceUnion.{u} S).ι) (g := q)
    (fg := (faceUnion S).ι ≫ q) rfl

theorem inclusion_trivial_cofibration (hS : S.Nonempty) :
    trivialCofibrations SSet.{u} (faceUnion.{u} S).ι := by
  have : WeakEquivalence (faceUnion.{u} S).ι := inclusion_weak S k hk hS
  exact (mem_trivialCofibrations_iff _).mpr
    ⟨(SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance, inferInstance⟩

end
end DaggerNativePartialFaceUnionContraction
