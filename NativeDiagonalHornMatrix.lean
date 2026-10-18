import NativeBisimplicialBox
import NativePartialFaceUnionGeometry

/-! The original diagonal-face matrix and its exact rows of proper face unions. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeDiagonalHornMatrix
noncomputable section

def missingFaces {n : ℕ} (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ)
    (a : (SSet.horn.{u} n k : SSet.{u}).obj h) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun j ↦ j ≠ k ∧ ∀ r, SSet.stdSimplex.asOrderHom a.val r ≠ j)

theorem missingFaces_nonempty {n : ℕ} (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ)
    (a : (SSet.horn.{u} n k : SSet.{u}).obj h) : (missingFaces k h a).Nonempty := by
  classical
  by_contra hn
  have hp : Set.range (SSet.stdSimplex.asOrderHom a.val) ∪ {k} ≠ Set.univ := a.property
  apply hp
  apply Set.eq_univ_of_forall
  intro j
  by_cases hj : j = k
  · exact Or.inr hj
  · apply Or.inl
    by_contra hr
    apply hn
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, ?_⟩⟩
    intro r he
    exact hr ⟨r, he⟩

theorem missingFaces_missing {n : ℕ} (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ)
    (a : (SSet.horn.{u} n k : SSet.{u}).obj h) : k ∉ missingFaces k h a := by
  intro hk
  exact (Finset.mem_filter.mp hk).2.1 rfl

theorem missingFaces_mono {n : ℕ} (k : Fin (n + 1)) {h l : SimplexCategoryᵒᵖ}
    (α : h ⟶ l) (a : (SSet.horn.{u} n k : SSet.{u}).obj h) :
    missingFaces k h a ⊆ missingFaces k l ((SSet.horn n k : SSet.{u}).map α a) := by
  intro j hj
  have hh := (Finset.mem_filter.mp hj).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1, ?_⟩
  intro r
  exact hh.2 (α.unop.toOrderHom r)

theorem faceUnion_mono {n : ℕ} {S T : Finset (Fin (n + 1))} (hST : S ⊆ T) :
    faceUnion.{u} S ≤ faceUnion T := by
  apply Finset.sup_le
  intro j hj
  exact Finset.le_sup (f := fun j ↦ SSet.stdSimplex.face {j}ᶜ) (hST hj)

def matrixRow {n : ℕ} (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ) :
    (boxRow ((SSet.horn.{u} n k : SSet.{u}).obj h) (Δ[n] : SSet.{u})).Subcomplex where
  obj v p := p.2 ∈ (faceUnion (missingFaces k h p.1)).obj v
  map α _ hp := (faceUnion (missingFaces k h _)).map α hp

theorem matrixRow_membership {n : ℕ} (k : Fin (n + 1)) (h v : SimplexCategoryᵒᵖ)
    (a : (SSet.horn.{u} n k : SSet.{u}).obj h) (b : (Δ[n] : SSet.{u}).obj v) :
    (a, b) ∈ (matrixRow k h).obj v ↔ ∃ j : Fin (n + 1), j ≠ k ∧
      (∀ r, SSet.stdSimplex.asOrderHom a.val r ≠ j) ∧
      ∀ s, SSet.stdSimplex.asOrderHom b s ≠ j := by
  change b ∈ (faceUnion (missingFaces k h a)).obj v ↔ _
  rw [mem_faceUnion]
  constructor
  · rintro ⟨j, hj, hb⟩
    exact ⟨j, (Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2, hb⟩
  · rintro ⟨j, hj, ha, hb⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, ha⟩, hb⟩

def hornMatrix (n : ℕ) (k : Fin (n + 1)) : BiSSet.{u} where
  obj h := matrixRow k h
  map α :=
    { app := fun v p ↦ ⟨((SSet.horn n k : SSet.{u}).map α p.val.1, p.val.2),
        faceUnion_mono (missingFaces_mono k α p.val.1) v p.property⟩
      naturality := by
        intros
        funext p
        apply Subtype.ext
        rfl }
  map_id h := by
    apply NatTrans.ext
    funext v p
    apply Subtype.ext
    change (((SSet.horn n k : SSet.{u}).map (𝟙 h)) p.val.1, p.val.2) = p.val
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp α β := by
    apply NatTrans.ext
    funext v p
    apply Subtype.ext
    change (((SSet.horn n k : SSet.{u}).map (α ≫ β)) p.val.1, p.val.2) = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

def matrixInclusion (n : ℕ) (k : Fin (n + 1)) :
    hornMatrix.{u} n k ⟶ box (SSet.horn.{u} n k) (Δ[n] : SSet.{u}) where
  app h := (matrixRow k h).ι
  naturality _ _ _ := by
    apply NatTrans.ext
    rfl

end
end DaggerNativeDiagonalHornMatrix
