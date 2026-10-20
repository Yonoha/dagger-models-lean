import NativeWalkingFullBlockPairingCore
import NativeWalkingRelativeRetainedTags
import NativeInnerPairing

/-!
The full original block pairing is regular.
The positive boundary/endpoint map therefore belongs to the original inner-left class.
-/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks
open DaggerNativeWalkingRelativeCells DaggerNativeWalkingRelativeCellCoverage
open DaggerNativeWalkingRelativeCellEquivalence DaggerNativeWalkingFullBlockPairingCore
open DaggerNativeWalkingRelativeRetainedTags DaggerNativeInnerPairing
universe u
namespace DaggerNativeWalkingFullBlockRegularity
noncomputable section

theorem ancestor_level (n : ℕ) (s t : UpperIndex.{u} n)
    (hd : (pairingCore n).d s = (pairingCore n).d t)
    (hst : (pairingCore n).AncestralRel s t) : level t.2.val < level s.2.val := by
  rcases s with ⟨d, s⟩
  rcases t with ⟨e, t⟩
  have hde : d = e := by
    change d + 1 = e + 1 at hd
    omega
  subst e
  obtain ⟨f, hf, _, hmap⟩ := hst.2
  haveI : Mono f := hf
  obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
  have hface : (ambient.{u} n).δ i t.val.val = (lower s).val.val := by
    rw [lower_val_index]
    exact hmap
  have hi : i ≠ cellIndex t := by
    intro hi
    have hh := hface
    rw [hi, ← lower_val_index] at hh
    have heq : lower t = lower s := Subtype.ext (Subtype.ext hh)
    have heq' : t = s := (cellEquivalence n d).symm.injective heq
    exact hst.1 (congrArg (Sigma.mk d) heq'.symm)
  have hi' : i ≠ endIndex t.val := hi
  have hh := face_level_strict t.val (lower s).val i hface hi' t.property (lower s).property
  simpa only [lower_level] using hh

def rank (n : ℕ) (s : UpperIndex.{u} n) : ℕ := n + 1 - (level s.2.val).val

theorem rank_decreases (n : ℕ) (s t : UpperIndex.{u} n)
    (hd : (pairingCore n).d s = (pairingCore n).d t)
    (hst : (pairingCore n).AncestralRel s t) : rank n s < rank n t := by
  have hl := ancestor_level n s t hd hst
  have hs : (level s.2.val).val ≤ n + 1 := Nat.le_of_lt_succ (level s.2.val).isLt
  change (level t.2.val).val < (level s.2.val).val at hl
  change n + 1 - (level s.2.val).val < n + 1 - (level t.2.val).val
  omega

instance pairingCoreRegular (n : ℕ) : (pairingCore.{u} n).IsRegular := by
  rw [SSet.Subcomplex.PairingCore.isRegular_iff]
  exact ⟨rank n, fun s t hd hst ↦ rank_decreases n s t hd hst⟩

theorem boundary_zero_innerAnodyne (n : ℕ) :
    DaggerNativeInnerHornFactorization.innerAnodyne.{u} (relative.{u} n).ι :=
  pairing_innerAnodyne (pairingCore n).pairing (pairingCoreInner n).pairing

end
end DaggerNativeWalkingFullBlockRegularity
