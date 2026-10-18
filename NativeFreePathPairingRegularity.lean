import NativeFreePathPairingCore

/-! Total original path weight makes the entire native spine pairing regular. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFreePathNerveWeight DaggerNativeFreePathPairingCells
open DaggerNativeFreePathPairingCore DaggerNativeFreePathFirstSubdivision
open DaggerNativeFreePathSubdivisionUniqueFace
universe u
namespace DaggerNativeFreePathPairingRegularity
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

theorem ancestral_weight_lt (s t : CellIndex V) (hd : s.1 = t.1)
    (h : (pairingCore V).AncestralRel s t) : weight (lower s) < weight (lower t) := by
  rcases s with ⟨n, c⟩
  rcases t with ⟨m, d⟩
  change n = m at hd
  subst m
  have hne : (⟨n, c⟩ : CellIndex V) ≠ ⟨n, d⟩ := h.1
  have hface : SSet.IsFace (X := nerve (Paths V)) (lower ⟨n, c⟩) (upper ⟨n, d⟩) := by
    have hf := h.2
    change SSet.IsFace (X := nerve (Paths V))
      ((nerve (Paths V)).δ (1 : Fin (n + 3)) (upper ⟨n, c⟩)) (upper ⟨n, d⟩) at hf
    rw [delta_one_upper ⟨n, c⟩] at hf
    exact hf
  obtain ⟨f, hf, _, he⟩ := hface
  have : Mono f := hf
  obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
  change (nerve (Paths V)).δ i (upper ⟨n, d⟩) = lower ⟨n, c⟩ at he
  by_cases hi0 : i = 0
  · subst i
    have hw := split_zero_weight_lt (lower ⟨n, d⟩) (split ⟨n, d⟩)
    change weight ((nerve (Paths V)).δ 0 (upper ⟨n, d⟩)) < _ at hw
    rw [he] at hw
    exact hw
  by_cases hi1 : i = 1
  · subst i
    have he' : lower ⟨n, d⟩ = lower ⟨n, c⟩ :=
      (delta_one_upper ⟨n, d⟩).symm.trans he
    exact (hne (lower_injective (congrArg
      (SSet.S.mk (X := nerve (Paths V))) he'.symm))).elim
  have hi : (1 : Fin (n + 3)) < i := by
    have h0 : i.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hi0
    have h1 : i.val ≠ 1 := by simpa only [Fin.ext_iff, Fin.val_one] using hi1
    simp only [Fin.lt_def, Fin.val_one]
    omega
  have hl := first_length_delta_after_one (upper ⟨n, d⟩) i hi
  rw [he] at hl
  have hc : 1 < ((lower ⟨n, c⟩).map' 0 1).length := c.property.2
  have he1 : ((lower ⟨n, c⟩).map' 0 1).length = 1 :=
    hl.trans (first_length_upper ⟨n, d⟩)
  exact (hc.ne' he1).elim

instance pairingCoreRegular : (pairingCore V).IsRegular := by
  rw [SSet.Subcomplex.PairingCore.isRegular_iff]
  refine ⟨fun s ↦ weight (lower s), fun s t hd h ↦ ?_⟩
  apply ancestral_weight_lt V s t ?_ h
  change s.1 + 1 = t.1 + 1 at hd
  omega

theorem generatorSpine_anodyne : SSet.anodyneExtensions (generatorSpine V).ι :=
  (pairingCore V).pairing.anodyneExtensions

end
end DaggerNativeFreePathPairingRegularity
