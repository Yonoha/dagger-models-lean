import ChosenNecklaceFlags
import ChosenNecklaceOrderLift

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {T : NecklaceCode} {n : ℕ} (F : Flag.{u} T n)

def selectedVertices : Finset (Fin (T.len + 1)) := by
  classical
  exact Finset.univ.filter (fun v ↦ ULift.up v ∈ F.chain (Fin.last n))

def selectedJoints : Finset (Fin (T.len + 1)) := by
  classical
  exact Finset.univ.filter (fun v ↦ ULift.up v ∈ F.chain 0)

theorem mem_selectedVertices (v : Fin (T.len + 1)) :
    v ∈ selectedVertices F ↔ ULift.up v ∈ F.chain (Fin.last n) := by
  simp [selectedVertices]

theorem mem_selectedJoints (v : Fin (T.len + 1)) :
    v ∈ selectedJoints F ↔ ULift.up v ∈ F.chain 0 := by
  simp [selectedJoints]

theorem selectedJoints_subset : selectedJoints F ⊆ selectedVertices F := by
  intro v hv
  exact (mem_selectedVertices F v).mpr
    (F.chain.monotone (Fin.zero_le _) ((mem_selectedJoints F v).mp hv))

theorem originalJoints_subset : T.joints ⊆ selectedJoints F := by
  intro v hv
  exact (mem_selectedJoints F v).mpr (F.joints (ULift.up v) hv)

theorem first_selectedJoint : (0 : Fin (T.len + 1)) ∈ selectedJoints F :=
  originalJoints_subset F T.first_mem

theorem last_selectedJoint : Fin.last T.len ∈ selectedJoints F :=
  originalJoints_subset F T.last_mem

def flankLen : ℕ := (selectedVertices F).card - 1

theorem flank_card : (selectedVertices F).card = flankLen F + 1 := by
  have h : 0 < (selectedVertices F).card := Finset.card_pos.mpr
    ⟨0, selectedJoints_subset F (first_selectedJoint F)⟩
  dsimp [flankLen]
  omega

def flankEmbedding : Fin (flankLen F + 1) ↪o Fin (T.len + 1) :=
  (selectedVertices F).orderEmbOfFin (flank_card F)

theorem flankEmbedding_first : flankEmbedding F 0 = 0 := by
  have h0 := selectedJoints_subset F (first_selectedJoint F)
  calc
    flankEmbedding F 0 =
        (selectedVertices F).min' (Finset.card_pos.mp ((flank_card F).symm ▸
          Nat.succ_pos (flankLen F))) :=
      Finset.orderEmbOfFin_zero (flank_card F) (Nat.succ_pos _)
    _ = 0 := le_antisymm ((selectedVertices F).min'_le 0 h0) (Fin.zero_le _)

theorem flankEmbedding_last : flankEmbedding F (Fin.last (flankLen F)) =
    Fin.last T.len := by
  have hN := selectedJoints_subset F (last_selectedJoint F)
  have h := Finset.orderEmbOfFin_last (flank_card F) (Nat.succ_pos (flankLen F))
  change flankEmbedding F (Fin.last (flankLen F)) = _ at h
  rw [h]
  exact le_antisymm (Fin.le_last _) ((selectedVertices F).le_max' _ hN)

/-- No new necklace representation: only finite order recoding in the original NecklaceCode. -/
def flankCode : NecklaceCode where
  len := flankLen F
  joints := Finset.univ.filter (fun v ↦ flankEmbedding F v ∈ selectedJoints F)
  first_mem := by simp [flankEmbedding_first, first_selectedJoint]
  last_mem := by simp [flankEmbedding_last, last_selectedJoint]

def flankVertex : Vertices.{u} (flankCode F) → Vertices.{u} T :=
  fun v ↦ ULift.up (flankEmbedding F v.down)

def flankFlag : Flag.{u} (flankCode F) n where
  chain :=
    { toFun i := flankVertex F ⁻¹' F.chain i
      monotone' i j hij := Set.preimage_mono (F.chain.monotone hij) }
  joints v hv := by
    have hm : flankEmbedding F v.down ∈ selectedJoints F := (Finset.mem_filter.mp hv).2
    exact (mem_selectedJoints F _).mp hm

def Flanked {U : NecklaceCode} (G : Flag.{u} U n) : Prop :=
  G.chain 0 = {v | v.down ∈ U.joints} ∧ G.chain (Fin.last n) = Set.univ

theorem flankFlag_flanked : Flanked (flankFlag F) := by
  constructor
  · ext v
    simp [flankFlag, flankVertex, flankCode, selectedJoints]
  · ext v
    simp only [flankFlag, OrderHom.coe_mk, Set.mem_preimage, Set.mem_univ, iff_true]
    exact (mem_selectedVertices F _).mp
      (Finset.orderEmbOfFin_mem (selectedVertices F) (flank_card F) v.down)

/-- Every flag set is retained as an actual image under the literal recoding inclusion. -/
theorem flankVertex_image (i : Fin (n + 1)) :
    flankVertex F '' (flankFlag F).chain i = F.chain i := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    have hlast := F.chain.monotone (Fin.le_last i) hv
    have hmem : v.down ∈ selectedVertices F := by
      apply (mem_selectedVertices F v.down).mpr
      simpa using hlast
    let w := ((selectedVertices F).orderIsoOfFin (flank_card F)).symm ⟨v.down, hmem⟩
    have hw : flankVertex F (ULift.up w) = v := by
      apply ULift.ext
      exact congrArg Subtype.val
        (((selectedVertices F).orderIsoOfFin (flank_card F)).apply_symm_apply ⟨v.down, hmem⟩)
    refine ⟨ULift.up w, ?_, hw⟩
    change flankVertex F (ULift.up w) ∈ F.chain i
    exact hw.symm ▸ hv

end

end DaggerOriginalFlagFlankification
