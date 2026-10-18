import NativeFreePathSpineComplementCoverage

/-! The actual lower and upper native cells for the free-path spine pairing. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFreePathNerveWeight DaggerNativeFreePathNerveWeightOperators
open DaggerNativePathFirstSplit DaggerNativeFreePathFirstSubdivision
open DaggerNativeFreePathSubdivisionUniqueFace
universe u
namespace DaggerNativeFreePathPairingCells
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

def LowerCell (n : ℕ) :=
  {c : ComposableArrows (Paths V) (n + 1) //
    c ∈ (nerve (Paths V)).nonDegenerate (n + 1) ∧ 1 < (c.map' 0 1).length}

def CellIndex := Σ n : ℕ, LowerCell V n

variable {V}

def lower (s : CellIndex V) : ComposableArrows (Paths V) (s.1 + 1) := s.2.val

def split (s : CellIndex V) : FirstSplit (V := V) ((lower s).map' 0 1) :=
  firstSplit _ (by
    have h : 1 < ((lower s).map' 0 1).length := s.2.property.2
    omega)

def upper (s : CellIndex V) : ComposableArrows (Paths V) (s.1 + 2) :=
  splitSimplex (lower s) (split s)

theorem delta_one_upper (s : CellIndex V) :
    (nerve (Paths V)).δ (1 : Fin (s.1 + 3)) (upper s) = lower s :=
  delta_one_split _ _

theorem lower_nonDegenerate (s : CellIndex V) :
    lower s ∈ (nerve (Paths V)).nonDegenerate (s.1 + 1) := s.2.property.1

theorem upper_nonDegenerate (s : CellIndex V) :
    upper s ∈ (nerve (Paths V)).nonDegenerate (s.1 + 2) :=
  split_nonDegenerate _ _ s.2.property.2 s.2.property.1

theorem lower_notMem (s : CellIndex V) :
    lower s ∉ (generatorSpine V).obj _ := by
  intro hs
  have hl := segment_length_le (lower s) 0 1 (Fin.zero_le _)
  have hp : 1 < ((lower s).map' 0 1).length := s.2.property.2
  change weight (lower s) ≤ 1 at hs
  change ((lower s).map' 0 1).length ≤ weight (lower s) at hl
  omega

theorem upper_notMem (s : CellIndex V) :
    upper s ∉ (generatorSpine V).obj _ := by
  change ¬ weight (upper s) ≤ 1
  rw [upper, split_weight]
  exact lower_notMem s

theorem first_length_upper (s : CellIndex V) : ((upper s).map' 0 1).length = 1 := rfl

theorem lower_injective {s t : CellIndex V}
    (h : SSet.S.mk (X := nerve (Paths V)) (lower s) = SSet.S.mk (lower t)) : s = t := by
  rcases s with ⟨n, c⟩
  rcases t with ⟨m, d⟩
  have hn : n = m := Nat.succ.inj (SSet.S.dim_eq_of_mk_eq h)
  subst m
  have hc : c.val = d.val := (SSet.S.ext_iff _ _).mp h
  have he : c = d := Subtype.ext hc
  cases he
  rfl

theorem upper_injective {s t : CellIndex V}
    (h : SSet.S.mk (X := nerve (Paths V)) (upper s) = SSet.S.mk (upper t)) : s = t := by
  rcases s with ⟨n, c⟩
  rcases t with ⟨m, d⟩
  have hn : n = m := by
    have hd := SSet.S.dim_eq_of_mk_eq h
    change n + 2 = m + 2 at hd
    omega
  subst m
  have he : upper ⟨n, c⟩ = upper ⟨n, d⟩ := (SSet.S.ext_iff _ _).mp h
  have hl := congrArg ((nerve (Paths V)).δ (1 : Fin (n + 3))) he
  have hl' : lower ⟨n, c⟩ = lower ⟨n, d⟩ :=
    (delta_one_upper ⟨n, c⟩).symm.trans (hl.trans (delta_one_upper ⟨n, d⟩))
  exact lower_injective (congrArg (SSet.S.mk (X := nerve (Paths V))) hl')

theorem upper_ne_lower (s t : CellIndex V) :
    SSet.S.mk (X := nerve (Paths V)) (upper s) ≠ SSet.S.mk (lower t) := by
  rcases s with ⟨n, c⟩
  rcases t with ⟨m, d⟩
  intro h
  have hm : m = n + 1 := by
    have hd := SSet.S.dim_eq_of_mk_eq h
    change n + 2 = m + 1 at hd
    omega
  subst m
  have he : upper ⟨n, c⟩ = lower ⟨n + 1, d⟩ := (SSet.S.ext_iff _ _).mp h
  have hl := congrArg (fun z : ComposableArrows (Paths V) (n + 2) ↦
    (z.map' 0 1).length) he
  have h1 : 1 = ((lower ⟨n + 1, d⟩).map' 0 1).length :=
    (first_length_upper ⟨n, c⟩).symm.trans hl
  exact (d.property.2.ne h1).elim

end
end DaggerNativeFreePathPairingCells
