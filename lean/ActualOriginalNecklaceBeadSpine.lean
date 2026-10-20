import ActualOriginalNecklaceSpineGeometry

/-! Each ORIGINAL interval bead has exactly its local standard spine as spine preimage. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeStandardSpineInner DaggerChosenRigidificationNecklace
universe u
namespace DaggerActualOriginalNecklaceBeadSpine
noncomputable section

variable {T : NecklaceCode} (b : T.Bead)

theorem embedding_mem (i : Fin (b.length + 1)) : b.embedding i ∈ b.interval :=
  (b.interval.orderIsoOfFin b.card_interval i).property

theorem embedding_step (i : Fin b.length) :
    (b.embedding i.succ).val = (b.embedding i.castSucc).val + 1 := by
  have ht := b.embedding.strictMono (Fin.castSucc_lt_succ (i := i))
  have hl : (b.embedding i.castSucc).val < (b.embedding i.succ).val := ht
  by_contra he
  have hgap : (b.embedding i.castSucc).val + 1 < (b.embedding i.succ).val := by omega
  let w : Fin (T.len + 1) :=
    ⟨(b.embedding i.castSucc).val + 1, lt_trans hgap (b.embedding i.succ).isLt⟩
  have hw : w ∈ b.interval := by
    have hm := Finset.mem_Icc.mp (embedding_mem b i.castSucc)
    have hn := Finset.mem_Icc.mp (embedding_mem b i.succ)
    apply Finset.mem_Icc.mpr
    constructor <;> change _ ≤ _
    · exact hm.1.trans (by change _ ≤ _ + 1; omega)
    · exact (show w ≤ b.embedding i.succ from Nat.le_of_lt hgap).trans hn.2
  let e := b.interval.orderIsoOfFin b.card_interval
  let k : Fin (b.length + 1) := e.symm ⟨w, hw⟩
  have hk : b.embedding k = w := congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)
  have hki : i.castSucc < k := by
    apply b.embedding.lt_iff_lt.mp
    rw [hk]
    change (b.embedding i.castSucc).val < (b.embedding i.castSucc).val + 1
    omega
  have hkj : k < i.succ := by
    apply b.embedding.lt_iff_lt.mp
    rw [hk]
    exact hgap
  have h1 : i.val < k.val := hki
  have h2 : k.val < i.val + 1 := hkj
  omega

theorem embedding_value (i : Fin (b.length + 1)) :
    (b.embedding i).val = b.left.val + i.val := by
  induction i using Fin.induction with
  | zero => rw [b.embedding_zero]; simp only [Fin.val_zero, Nat.add_zero]
  | succ i ih =>
    rw [embedding_step, ih]
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega

theorem spine_preimage_bead :
    (spine.{u} T.len).preimage (b.faceIso.hom ≫ b.face.ι) = spine b.length := by
  ext q x
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      change (b.faceIso.hom ≫ b.face.ι).app (op ⦋d⦌) x ∈
        (spine T.len).obj (op ⦋d⦌) ↔ x ∈ (spine b.length).obj (op ⦋d⦌)
      rw [mem_spine_iff, mem_spine_iff]
      change (b.embedding (SSet.stdSimplex.asOrderHom x (Fin.last d))).val ≤
        (b.embedding (SSet.stdSimplex.asOrderHom x 0)).val + 1 ↔ _
      rw [embedding_value, embedding_value]
      omega

end
end DaggerActualOriginalNecklaceBeadSpine
