import OriginalIntervalFlagComposition

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerChosenRigidificationNecklace.NecklaceThickening

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- Split any original interval at an actual joint of the original necklace. -/
def intervalFlagSplitIso (T : NecklaceCode) (a k b : Fin (T.len + 1))
    (hak : a ≤ k) (hkb : k ≤ b) (hk : k ∈ T.joints) :
    flagSSet.{u} (intervalCode T a b (hak.trans hkb)) ≅
      flagSSet (intervalCode T a k hak) ⊗ flagSSet (intervalCode T k b hkb) :=
  intervalOuterHomIso T a b (hak.trans hkb) ≪≫
    jointSplitIso k hk hak hkb ≪≫
      tensorIso (intervalOuterHomIso T a k hak).symm (intervalOuterHomIso T k b hkb).symm

theorem intervalFlagSplitIso_inv (T : NecklaceCode) (a k b : Fin (T.len + 1))
    (hak : a ≤ k) (hkb : k ≤ b) (hk : k ∈ T.joints) :
    (intervalFlagSplitIso.{u} T a k b hak hkb hk).inv =
      intervalFlagCompose T a k b hak hkb := by
  simp [intervalFlagSplitIso, intervalFlagCompose, jointSplitIso_inv, Category.assoc]

theorem intervalFlagSplit_recombine (T : NecklaceCode) (a k b : Fin (T.len + 1))
    (hak : a ≤ k) (hkb : k ≤ b) (hk : k ∈ T.joints) {n : ℕ}
    (F : Flag.{u} (intervalCode T a b (hak.trans hkb)) n) :
    (intervalFlagCompose T a k b hak hkb).app (op ⦋n⦌)
        ((intervalFlagSplitIso T a k b hak hkb hk).hom.app (op ⦋n⦌) F) = F := by
  rw [← intervalFlagSplitIso_inv T a k b hak hkb hk]
  exact congrArg (fun f ↦ f.app (op ⦋n⦌) F)
    (intervalFlagSplitIso.{u} T a k b hak hkb hk).hom_inv_id

theorem intervalFlagSplit_compose (T : NecklaceCode) (a k b : Fin (T.len + 1))
    (hak : a ≤ k) (hkb : k ≤ b) (hk : k ∈ T.joints) {n : ℕ}
    (F : Flag.{u} (intervalCode T a k hak) n) (G : Flag.{u} (intervalCode T k b hkb) n) :
    (intervalFlagSplitIso T a k b hak hkb hk).hom.app (op ⦋n⦌)
        ((intervalFlagCompose T a k b hak hkb).app (op ⦋n⦌) (F, G)) = (F, G) := by
  rw [← intervalFlagSplitIso_inv T a k b hak hkb hk]
  exact congrArg (fun f ↦ f.app (op ⦋n⦌) (F, G))
    (intervalFlagSplitIso.{u} T a k b hak hkb hk).inv_hom_id

/-- The three original interval flags compose associatively, before taking any quotient. -/
theorem intervalFlagCompose_assoc (T : NecklaceCode) (a k l b : Fin (T.len + 1))
    (hak : a ≤ k) (hkl : k ≤ l) (hlb : l ≤ b) {n : ℕ}
    (F : Flag.{u} (intervalCode T a k hak) n)
    (M : Flag.{u} (intervalCode T k l hkl) n)
    (G : Flag.{u} (intervalCode T l b hlb) n) :
    (intervalFlagCompose T a l b (hak.trans hkl) hlb).app (op ⦋n⦌)
        ((intervalFlagCompose T a k l hak hkl).app (op ⦋n⦌) (F, M), G) =
      (intervalFlagCompose T a k b hak (hkl.trans hlb)).app (op ⦋n⦌)
        (F, (intervalFlagCompose T k l b hkl hlb).app (op ⦋n⦌) (M, G)) := by
  apply ((intervalOuterHomIso.{u} T a b (hak.trans (hkl.trans hlb))).app
    (op ⦋n⦌)).toEquiv.injective
  refine CategoryTheory.Functor.ext (fun i ↦ JointPath.ext ?_)
  change (((intervalOuterHomIso T a b (hak.trans (hkl.trans hlb))).hom.app (op ⦋n⦌)
      ((intervalFlagCompose T a l b (hak.trans hkl) hlb).app (op ⦋n⦌)
        ((intervalFlagCompose T a k l hak hkl).app (op ⦋n⦌) (F, M), G))).obj i).I =
    (((intervalOuterHomIso T a b (hak.trans (hkl.trans hlb))).hom.app (op ⦋n⦌)
      ((intervalFlagCompose T a k b hak (hkl.trans hlb)).app (op ⦋n⦌)
        (F, (intervalFlagCompose T k l b hkl hlb).app (op ⦋n⦌) (M, G)))).obj i).I
  rw [intervalOuterHomIso_image, intervalOuterHomIso_image]
  let A := mapVertices (intervalι T a k hak) '' F.chain i
  let B := mapVertices (intervalι T k l hkl) '' M.chain i
  let C := mapVertices (intervalι T l b hlb) '' G.chain i
  calc
    _ = (A ∪ B) ∪ C :=
      (intervalFlagCompose_image T a l b (hak.trans hkl) hlb
        ((intervalFlagCompose T a k l hak hkl).app (op ⦋n⦌) (F, M)) G i).trans
          (congrArg (fun Z ↦ Z ∪ C) (intervalFlagCompose_image T a k l hak hkl F M i))
    _ = A ∪ (B ∪ C) := Set.union_assoc A B C
    _ = _ := ((intervalFlagCompose_image T a k b hak (hkl.trans hlb) F
      ((intervalFlagCompose T k l b hkl hlb).app (op ⦋n⦌) (M, G)) i).trans
        (congrArg (fun Z ↦ A ∪ Z) (intervalFlagCompose_image T k l b hkl hlb M G i))).symm

/-- The two specified cuts of the same flag admit a common triple refinement,
with the exact two split outputs and no distinctness assumption on the cuts. -/
theorem intervalFlag_common_refinement (T : NecklaceCode) (a k l b : Fin (T.len + 1))
    (hak : a ≤ k) (hkl : k ≤ l) (hlb : l ≤ b)
    (hk : k ∈ T.joints) (hl : l ∈ T.joints) {n : ℕ}
    (H : Flag.{u} (intervalCode T a b (hak.trans (hkl.trans hlb))) n) :
    ∃ (F : Flag.{u} (intervalCode T a k hak) n)
      (M : Flag.{u} (intervalCode T k l hkl) n)
      (G : Flag.{u} (intervalCode T l b hlb) n),
      (intervalFlagSplitIso T a k b hak (hkl.trans hlb) hk).hom.app (op ⦋n⦌) H =
        (F, (intervalFlagCompose T k l b hkl hlb).app (op ⦋n⦌) (M, G)) ∧
      (intervalFlagSplitIso T a l b (hak.trans hkl) hlb hl).hom.app (op ⦋n⦌) H =
        ((intervalFlagCompose T a k l hak hkl).app (op ⦋n⦌) (F, M), G) := by
  let A := (intervalFlagSplitIso T a k b hak (hkl.trans hlb) hk).hom.app (op ⦋n⦌) H
  let B := (intervalFlagSplitIso T k l b hkl hlb hl).hom.app (op ⦋n⦌) A.2
  have hB : (intervalFlagCompose T k l b hkl hlb).app (op ⦋n⦌) (B.1, B.2) = A.2 :=
    intervalFlagSplit_recombine T k l b hkl hlb hl A.2
  refine ⟨A.1, B.1, B.2, Prod.ext rfl hB.symm, ?_⟩
  have he : (intervalFlagCompose T a l b (hak.trans hkl) hlb).app (op ⦋n⦌)
      ((intervalFlagCompose T a k l hak hkl).app (op ⦋n⦌) (A.1, B.1), B.2) = H := by
    rw [intervalFlagCompose_assoc, hB]
    exact intervalFlagSplit_recombine T a k b hak (hkl.trans hlb) hk H
  exact (congrArg
    (fun Z ↦ (intervalFlagSplitIso T a l b (hak.trans hkl) hlb hl).hom.app (op ⦋n⦌) Z)
    he).symm.trans (intervalFlagSplit_compose T a l b (hak.trans hkl) hlb hl _ B.2)

/-- Normalize only the full-interval presentation, retaining the entire original flag space. -/
def wholeIntervalFlagIso (S : NecklaceCode) :
    flagSSet.{u} S ≅ flagSSet (intervalCode S 0 (Fin.last S.len) (Fin.zero_le _)) :=
  outerFlagIso S ≪≫ (intervalOuterHomIso S 0 (Fin.last S.len) (Fin.zero_le _)).symm

theorem wholeIntervalFlagIso_split (S : NecklaceCode) (k : Fin (S.len + 1))
    (hk : k ∈ S.joints) :
    (wholeIntervalFlagIso.{u} S).hom ≫
        (intervalFlagSplitIso S 0 k (Fin.last S.len) (Fin.zero_le k) (Fin.le_last k) hk).hom =
      (cutFlagIso S k hk).hom := by
  simp [wholeIntervalFlagIso, intervalFlagSplitIso, cutFlagIso, Category.assoc]

/-- Two cuts of the original full flag, not merely an isomorphic interval model,
are obtained from one triple of flags on the original prefix, middle interval and suffix. -/
theorem fullFlag_common_refinement (S : NecklaceCode) (k l : Fin (S.len + 1))
    (hkl : k ≤ l) (hk : k ∈ S.joints) (hl : l ∈ S.joints) {n : ℕ} (H : Flag.{u} S n) :
    ∃ (F : Flag.{u} (cutLeft S k) n)
      (M : Flag.{u} (intervalCode S k l hkl) n) (G : Flag.{u} (cutRight S l) n),
      (cutFlagIso S k hk).hom.app (op ⦋n⦌) H =
        (F, (intervalFlagCompose S k l (Fin.last S.len) hkl (Fin.le_last l)).app
          (op ⦋n⦌) (M, G)) ∧
      (cutFlagIso S l hl).hom.app (op ⦋n⦌) H =
        ((intervalFlagCompose S 0 k l (Fin.zero_le k) hkl).app (op ⦋n⦌) (F, M), G) := by
  obtain ⟨F, M, G, hF, hG⟩ := intervalFlag_common_refinement S 0 k l (Fin.last S.len)
    (Fin.zero_le k) hkl (Fin.le_last l) hk hl
    ((wholeIntervalFlagIso S).hom.app (op ⦋n⦌) H)
  refine ⟨F, M, G, ?_, ?_⟩
  · exact (congrArg (fun f ↦ f.app (op ⦋n⦌) H) (wholeIntervalFlagIso_split S k hk)).symm.trans hF
  · exact (congrArg (fun f ↦ f.app (op ⦋n⦌) H) (wholeIntervalFlagIso_split S l hl)).symm.trans hG

end

end DaggerOriginalProductGadget
