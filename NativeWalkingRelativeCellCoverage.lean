import NativeWalkingRelativeCells

/-! Every original relative nondegenerate cell lies in exactly one of the two shifted classes. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerNativeWalkingRelativeCells
universe u
namespace DaggerNativeWalkingRelativeCellCoverage
noncomputable section

def castCell {n d e : ℕ} (he : d = e) (x : Cell.{u} n d) : Cell.{u} n e := he ▸ x

theorem toN_castCell {n d e : ℕ} (he : d = e) (x : Cell.{u} n d) :
    toN (castCell he x) = toN x := by cases he; rfl

theorem endTag_castCell {n d e : ℕ} (he : d = e) (x : Cell.{u} n d) :
    endTag (castCell he x) = endTag x := by cases he; rfl

theorem lower_coverage {n d : ℕ} (x : Cell.{u} n d) (ht : endTag x = true) :
    ∃ (e : ℕ) (y : LowerCell.{u} n e), toN y.val = toN x := by
  have hd : 1 ≤ d := (Nat.succ_pos n).trans_le (dim_bound x)
  have he : d - 1 + 1 = d := Nat.sub_add_cancel hd
  let y := castCell he.symm x
  have hy : endTag y = true := by simpa only [y, endTag_castCell] using ht
  exact ⟨d - 1, ⟨y, hy⟩, toN_castCell he.symm x⟩

theorem upper_coverage {n d : ℕ} (x : Cell.{u} n d) (ht : endTag x = false) :
    ∃ (e : ℕ) (y : UpperCell.{u} n e), toN y.val = toN x := by
  have he : d - 2 + 2 = d := Nat.sub_add_cancel (upper_dim_bound x ht)
  let y := castCell he.symm x
  have hy : endTag y = false := by simpa only [y, endTag_castCell] using ht
  exact ⟨d - 2, ⟨y, hy⟩, toN_castCell he.symm x⟩

def tagN {n : ℕ} (x : (relative.{u} n).N) : Bool :=
  endTag ((cellEquiv n) x).2

theorem tagN_toN {n d : ℕ} (x : Cell.{u} n d) : tagN (toN x) = endTag x := rfl

theorem whole_cell_partition {n : ℕ} (x : (relative.{u} n).N) :
    (∃ (d : ℕ) (y : UpperCell.{u} n d), toN y.val = x) ∨
      (∃ (d : ℕ) (y : LowerCell.{u} n d), toN y.val = x) := by
  let c := (cellEquiv n) x
  have hc : toN c.2 = x := (cellEquiv n).left_inv x
  cases ht : endTag c.2
  · obtain ⟨d, y, hy⟩ := upper_coverage c.2 ht
    exact Or.inl ⟨d, y, hy.trans hc⟩
  · obtain ⟨d, y, hy⟩ := lower_coverage c.2 ht
    exact Or.inr ⟨d, y, hy.trans hc⟩

theorem disjoint_classes {n d e : ℕ} (x : UpperCell.{u} n d) (y : LowerCell.{u} n e) :
    toN x.val ≠ toN y.val := by
  intro he
  have hh := congrArg tagN he
  change endTag x.val = endTag y.val at hh
  rw [x.property, y.property] at hh
  exact Bool.false_ne_true hh

def UpperIndex (n : ℕ) := Σ d, UpperCell.{u} n d
def LowerIndex (n : ℕ) := Σ d, LowerCell.{u} n d

def upperToN {n : ℕ} (x : UpperIndex.{u} n) : (relative.{u} n).N := toN x.2.val
def lowerToN {n : ℕ} (x : LowerIndex.{u} n) : (relative.{u} n).N := toN x.2.val

theorem upperToN_injective {n : ℕ} : Function.Injective (upperToN.{u} (n := n)) := by
  intro s t he
  rcases s with ⟨d, s⟩
  rcases t with ⟨e, t⟩
  have hd : d = e := by
    have hh := congrArg (fun z : (relative.{u} n).N ↦ z.dim) he
    change d + 2 = e + 2 at hh
    omega
  subst e
  have hh := (SSet.Subcomplex.N.eq_iff_sMk_eq _ _).mp he
  have hv : s.val.val = t.val.val := (SSet.S.ext_iff _ _).mp hh
  exact congrArg (Sigma.mk d) (Subtype.ext (Subtype.ext hv))

theorem lowerToN_injective {n : ℕ} : Function.Injective (lowerToN.{u} (n := n)) := by
  intro s t he
  rcases s with ⟨d, s⟩
  rcases t with ⟨e, t⟩
  have hd : d = e := by
    have hh := congrArg (fun z : (relative.{u} n).N ↦ z.dim) he
    change d + 1 = e + 1 at hh
    omega
  subst e
  have hh := (SSet.Subcomplex.N.eq_iff_sMk_eq _ _).mp he
  have hv : s.val.val = t.val.val := (SSet.S.ext_iff _ _).mp hh
  exact congrArg (Sigma.mk d) (Subtype.ext (Subtype.ext hv))

end
end DaggerNativeWalkingRelativeCellCoverage
