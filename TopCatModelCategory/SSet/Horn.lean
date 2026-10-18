import TopCatModelCategory.CommSq
import TopCatModelCategory.SSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

universe u

open CategoryTheory Category Limits Simplicial Opposite
  MonoidalCategory CartesianMonoidalCategory

namespace SSet

variable {n : ℕ}

/-lemma horn_eq_iSup (i : Fin (n + 1)) :
    horn.{u} n i =
      ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ := by
  ext m j
  simp [stdSimplex.face, horn]
  change ¬ _ ↔ _
  simp [Set.eq_univ_iff_forall]
  rfl

lemma face_le_horn (i j : Fin (n + 1)) (h : i ≠ j) :
    stdSimplex.face.{u} {i}ᶜ ≤ horn n j := by
  rw [horn_eq_iSup]
  exact le_iSup (fun (k : ({j}ᶜ : Set (Fin (n + 1)))) ↦ stdSimplex.face.{u} {k.1}ᶜ) ⟨i, h⟩-/

lemma horn_le_boundary (i : Fin (n + 1)) :
    horn.{u} n i ≤ boundary n := by
  rw [horn_eq_iSup]
  simp
  intros
  apply face_le_boundary

instance (i : Fin (n + 1)) : HasDimensionLT (horn.{u} n i) n :=
  Subcomplex.hasDimensionLT_of_le
    (horn_le_boundary i) n

lemma horn_obj_eq_top (i : Fin (n + 1)) (m : ℕ) (h : m + 1 < n) :
    (horn.{u} n i).obj (op ⦋m⦌) = ⊤ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  obtain ⟨j, hij, hj⟩ : ∃ (j : Fin (n + 1)), j ≠ i ∧ j ∉ Set.range f.toOrderHom := by
    by_contra!
    have : Finset.image f.toOrderHom ⊤ ∪ {i} = ⊤ := by
      ext k
      simp
      by_cases k = i <;> aesop
    have := (congr_arg Finset.card this).symm.le.trans (Finset.card_union_le _ _)
    simp only [SimplexCategory.len_mk, Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, add_le_add_iff_right] at this
    have := this.trans Finset.card_image_le
    simp at this
    omega
  simp [horn_eq_iSup]
  exact ⟨j, hij, fun k hk ↦ hj ⟨k, hk⟩⟩

lemma stdSimplex.subcomplex_le_horn_iff
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (i : Fin (n + 2)) :
    A ≤ horn (n + 1) i ↔ ¬ (face {i}ᶜ ≤ A) := by
  constructor
  · intro hA h
    replace h := h.trans hA
    rw [face_singleton_compl, Subcomplex.ofSimplex_le_iff,
      mem_horn_iff] at h
    apply h
    change Set.range (Fin.succAboveOrderEmb i).toOrderHom ∪ _ = _
    rw [Fin.range_succAboveOrderEmb]
    exact Set.compl_union_self {i}
  · intro h
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    by_cases hd : d < n
    · simp [horn_obj_eq_top i d (by omega)]
    · simp only [not_lt] at hd
      obtain ⟨⟨S, hS⟩, rfl⟩ := stdSimplex.nonDegenerateEquiv'.symm.surjective x
      dsimp at hS
      simp only [stdSimplex.nonDegenerateEquiv'_symm_mem_iff_face_le] at hx ⊢
      obtain hd | rfl := hd.lt_or_eq
      · obtain rfl : S = Finset.univ := by
          rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
          exact le_antisymm (S.card_le_univ.trans (by simp)) (by omega)
        exfalso
        exact h (le_trans (by simp [face_le_face_iff]) hx)
      · replace hS : Sᶜ.card = 1 := by
          have := S.card_compl_add_card
          rw [Fintype.card_fin] at this
          omega
        obtain ⟨j, rfl⟩ : ∃ j, S = {j}ᶜ := by
          obtain ⟨j, hj⟩ | h :=
            Finset.Nonempty.exists_eq_singleton_or_nontrivial (s := Sᶜ) (by
              rw [← Finset.card_pos]
              omega)
          · exact ⟨j, by simp [← hj]⟩
          · rw [← Finset.one_lt_card_iff_nontrivial] at h
            omega
        apply face_le_horn
        rintro rfl
        exact h hx

lemma objEquiv_symm_δ_mem_horn_iff {n : ℕ} (i j : Fin (n + 2)) :
    stdSimplex.objEquiv.symm (SimplexCategory.δ i) ∈ (horn _ j).obj _ ↔
      i ≠ j := by
  dsimp
  erw [← Subcomplex.ofSimplex_le_iff,
    ← stdSimplex.face_singleton_compl]
  refine ⟨?_, face_le_horn _ _⟩
  rintro h rfl
  simp [stdSimplex.subcomplex_le_horn_iff] at h

lemma objEquiv_symm_δ_notMem_horn_iff {n : ℕ} (i j : Fin (n + 2)) :
    stdSimplex.objEquiv.symm (SimplexCategory.δ i) ∉ (horn _ j).obj _ ↔
      i = j := by
  rw [objEquiv_symm_δ_mem_horn_iff]
  simp

lemma objEquiv_symm_notMem_horn_of_isIso {n : ℕ} (i : Fin (n + 1))
    {d : SimplexCategory} (f : d ⟶ ⦋n⦌) [IsIso f] :
    stdSimplex.objEquiv.symm f ∉ (horn n i).obj (op d) := by
  induction d using SimplexCategory.rec with | _ d
  obtain rfl : n = d :=
    le_antisymm
      (SimplexCategory.len_le_of_epi f)
      (SimplexCategory.len_le_of_mono f)
  obtain rfl := SimplexCategory.eq_id_of_isIso f
  rw [horn_eq_iSup]
  aesop



namespace horn₁

variable (i : Fin 2)

lemma eq_face : horn.{u} 1 i = stdSimplex.face {i} := by
  rw [horn_eq_iSup]
  fin_cases i
  · letI : Unique ({0}ᶜ : Set (Fin 2)) :=
      { default := ⟨1, by simp⟩
        uniq := by rintro ⟨a, _⟩; fin_cases a <;> aesop }
    dsimp
    rw [iSup_unique]
    rfl
  · letI : Unique ({1}ᶜ : Set (Fin 2)) :=
      { default := ⟨0, by simp⟩
        uniq := by rintro ⟨a, _⟩; fin_cases a <;> aesop }
    dsimp
    rw [iSup_unique]
    rfl

lemma ι_eq : (horn.{u} 1 i).ι = const.{u} (stdSimplex.obj₀Equiv.{u}.symm i) := by
  rw [← Subcomplex.isoOfEq_hom_ι (eq_face i), stdSimplex.face_singleton_ι_eq_const, comp_const]

noncomputable def iso : Δ[0] ≅ (horn 1 i : SSet.{u}) :=
  stdSimplex.faceSingletonIso _ ≪≫ Subcomplex.isoOfEq (eq_face i).symm

@[reassoc (attr := simp)]
lemma iso₁_hom_ι : (iso.{u} 1).hom ≫ Λ[1, 1].ι = stdSimplex.δ 0 := by
  rw [ι_eq, comp_const]
  apply yonedaEquiv.injective
  ext j
  fin_cases j
  rfl

@[reassoc (attr := simp)]
lemma iso₁_inv_δ_zero : (iso.{u} 1).inv ≫ stdSimplex.δ 0 = Λ[1, 1].ι := by
  rw [← iso₁_hom_ι, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma iso₀_hom_ι : (iso.{u} 0).hom ≫ Λ[1, 0].ι = stdSimplex.δ 1 := by
  rw [ι_eq, comp_const]
  apply yonedaEquiv.injective
  ext j
  fin_cases j
  rfl

@[reassoc (attr := simp)]
lemma iso₀_inv_δ_one : (iso.{u} 0).inv ≫ stdSimplex.δ 1 = Λ[1, 0].ι := by
  rw [← iso₀_hom_ι, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma whiskerLeft_iso₁_inv_comp_rightUnitor_hom (X : SSet.{u}) :
    X ◁ (horn₁.iso 1).inv ≫ (stdSimplex.rightUnitor X).hom = fst _ _ := by
  rw [← cancel_epi (X ◁ (horn₁.iso 1).hom), ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, id_comp, whiskerLeft_fst]
  rfl

@[reassoc (attr := simp)]
lemma whiskerLeft_iso₀_inv_comp_rightUnitor_hom (X : SSet.{u}) :
    X ◁ (horn₁.iso 0).inv ≫ (stdSimplex.rightUnitor X).hom = fst _ _ := by
  rw [← cancel_epi (X ◁ (horn₁.iso 0).hom), ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id, id_comp, whiskerLeft_fst]
  rfl

lemma eq_ofSimplex : Λ[1, i] = Subcomplex.ofSimplex.{u} (stdSimplex.obj₀Equiv.symm i) := by
  rw [eq_face, stdSimplex.face_singleton_eq_ofSimplex]

lemma eq_objMk_const {d : ℕ} (x : Δ[1] _⦋d⦌) (hx : x ∈ Λ[1, i].obj _) :
    x = stdSimplex.objMk (n := .mk 1) (OrderHom.const _ i) := by
  rw [eq_ofSimplex] at hx
  obtain ⟨⟨f⟩, rfl⟩ := hx
  obtain rfl : f = SimplexCategory.const _ _ 0 := Subsingleton.elim _ _
  rfl

end horn₁

end SSet
