import ChosenNecklacePointMaps
import ChosenNecklaceWedgeBeads

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T U : NecklaceCode) {n : ℕ}

def leftPreSimplex (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, ((wedge T U).inclusion.app _ x i).val ≤ T.len) :
    (Δ[T.len] : SSet.{u}).obj (op ⦋n⦌) :=
  SSet.stdSimplex.objMk
    ⟨fun i ↦ wedgeLeftDown T U ((wedge T U).inclusion.app _ x i) (hx i),
      fun _ _ h ↦ SSet.stdSimplex.monotone_apply ((wedge T U).inclusion.app _ x) h⟩

def rightPreSimplex (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, T.len ≤ ((wedge T U).inclusion.app _ x i).val) :
    (Δ[U.len] : SSet.{u}).obj (op ⦋n⦌) :=
  SSet.stdSimplex.objMk
    ⟨fun i ↦ wedgeRightDown T U ((wedge T U).inclusion.app _ x i) (hx i),
      fun _ _ h ↦ Nat.sub_le_sub_right
        (show (((wedge T U).inclusion.app _ x) _).val ≤
          (((wedge T U).inclusion.app _ x) _).val from
            SSet.stdSimplex.monotone_apply ((wedge T U).inclusion.app _ x) h) T.len⟩

theorem leftPreSimplex_mem (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, ((wedge T U).inclusion.app _ x i).val ≤ T.len) :
    leftPreSimplex T U x hx ∈ T.complex.obj (op ⦋n⦌) := by
  have hm := ((wedge T U).complexIso.hom.app _ x).property
  rcases ((wedge T U).mem_complex_iff _).mp hm with h | ⟨b, h⟩
  · apply (T.mem_complex_iff _).mpr
    left
    intro i
    apply Fin.ext
    change ((wedge T U).inclusion.app _ x i).val = 0
    exact congrArg Fin.val (h i)
  · rcases wedge_bead_cases T U b with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · apply (T.mem_complex_iff _).mpr
      right
      refine ⟨c, fun i ↦ ?_⟩
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp (h i)
      exact Finset.mem_Icc.mpr ⟨hl, hr⟩
    · apply constant_mem_complex T (Fin.last T.len)
      intro i
      apply Fin.ext
      have hl := (Finset.mem_Icc.mp (h i)).1
      change T.len + c.left.val ≤ ((wedge T U).inclusion.app _ x i).val at hl
      change ((wedge T U).inclusion.app _ x i).val = T.len
      have hh := hx i
      omega

theorem rightPreSimplex_mem (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, T.len ≤ ((wedge T U).inclusion.app _ x i).val) :
    rightPreSimplex T U x hx ∈ U.complex.obj (op ⦋n⦌) := by
  have hm := ((wedge T U).complexIso.hom.app _ x).property
  rcases ((wedge T U).mem_complex_iff _).mp hm with h | ⟨b, h⟩
  · apply constant_mem_complex U 0
    intro i
    apply Fin.ext
    change ((wedge T U).inclusion.app _ x i).val - T.len = 0
    have hh := congrArg Fin.val (h i)
    change ((wedge T U).inclusion.app _ x i).val = 0 at hh
    omega
  · rcases wedge_bead_cases T U b with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · apply constant_mem_complex U 0
      intro i
      apply Fin.ext
      have hr := (Finset.mem_Icc.mp (h i)).2
      change ((wedge T U).inclusion.app _ x i).val ≤ c.right.val at hr
      change ((wedge T U).inclusion.app _ x i).val - T.len = 0
      have hh := c.right.isLt
      omega
    · apply (U.mem_complex_iff _).mpr
      right
      refine ⟨c, fun i ↦ ?_⟩
      obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp (h i)
      change T.len + c.left.val ≤ ((wedge T U).inclusion.app _ x i).val at hl
      change ((wedge T U).inclusion.app _ x i).val ≤ T.len + c.right.val at hr
      apply Finset.mem_Icc.mpr
      constructor
      · change c.left.val ≤ ((wedge T U).inclusion.app _ x i).val - T.len
        omega
      · change ((wedge T U).inclusion.app _ x i).val - T.len ≤ c.right.val
        omega

def leftLift (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, ((wedge T U).inclusion.app _ x i).val ≤ T.len) :
    (toSSet.{u} T).obj (op ⦋n⦌) :=
  T.complexIso.inv.app _ ⟨leftPreSimplex T U x hx, leftPreSimplex_mem T U x hx⟩

def rightLift (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, T.len ≤ ((wedge T U).inclusion.app _ x i).val) :
    (toSSet.{u} U).obj (op ⦋n⦌) :=
  U.complexIso.inv.app _ ⟨rightPreSimplex T U x hx, rightPreSimplex_mem T U x hx⟩

theorem leftLift_inclusion (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, ((wedge T U).inclusion.app _ x i).val ≤ T.len) :
    T.inclusion.app _ (leftLift T U x hx) = leftPreSimplex T U x hx := by
  have h := congrFun (NatTrans.congr_app T.complexIso.inv_hom_id (op ⦋n⦌))
    ⟨leftPreSimplex T U x hx, leftPreSimplex_mem T U x hx⟩
  exact congrArg Subtype.val h

theorem rightLift_inclusion (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, T.len ≤ ((wedge T U).inclusion.app _ x i).val) :
    U.inclusion.app _ (rightLift T U x hx) = rightPreSimplex T U x hx := by
  have h := congrFun (NatTrans.congr_app U.complexIso.inv_hom_id (op ⦋n⦌))
    ⟨rightPreSimplex T U x hx, rightPreSimplex_mem T U x hx⟩
  exact congrArg Subtype.val h

theorem wedgeιLeft_apply (x : (toSSet.{u} T).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    (wedge T U).inclusion.app _ ((wedgeιLeft T U).app _ x) i =
      wedgeLeft T U (T.inclusion.app _ x i) := by
  have h := congrFun (NatTrans.congr_app (wedgeιLeft_inclusion.{u} T U) (op ⦋n⦌)) x
  exact congrArg (fun y : (Δ[(wedge T U).len] : SSet.{u}).obj (op ⦋n⦌) ↦ y i) h

theorem wedgeιRight_apply (x : (toSSet.{u} U).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    (wedge T U).inclusion.app _ ((wedgeιRight T U).app _ x) i =
      wedgeRight T U (U.inclusion.app _ x i) := by
  have h := congrFun (NatTrans.congr_app (wedgeιRight_inclusion.{u} T U) (op ⦋n⦌)) x
  exact congrArg (fun y : (Δ[(wedge T U).len] : SSet.{u}).obj (op ⦋n⦌) ↦ y i) h

theorem wedgeιLeft_leftLift (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, ((wedge T U).inclusion.app _ x i).val ≤ T.len) :
    (wedgeιLeft T U).app _ (leftLift T U x hx) = x := by
  apply necklace_simplex_ext
  intro i
  rw [wedgeιLeft_apply, leftLift_inclusion]
  exact Fin.ext rfl

theorem wedgeιRight_rightLift (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌))
    (hx : ∀ i, T.len ≤ ((wedge T U).inclusion.app _ x i).val) :
    (wedgeιRight T U).app _ (rightLift T U x hx) = x := by
  apply necklace_simplex_ext
  intro i
  rw [wedgeιRight_apply, rightLift_inclusion]
  apply Fin.ext
  change T.len + ((((wedge T U).inclusion.app _ x) i).val - T.len) = _
  have hh := hx i
  omega

theorem wedge_degree_cover (x : (toSSet.{u} (wedge T U)).obj (op ⦋n⦌)) :
    (∃ y, (wedgeιLeft T U).app _ y = x) ∨ (∃ y, (wedgeιRight T U).app _ y = x) := by
  have hm := ((wedge T U).complexIso.hom.app _ x).property
  rcases ((wedge T U).mem_complex_iff _).mp hm with h | ⟨b, h⟩
  · have hx : ∀ i, ((wedge T U).inclusion.app _ x i).val ≤ T.len := by
      intro i
      have hi := congrArg Fin.val (h i)
      change ((wedge T U).inclusion.app _ x i).val = 0 at hi
      omega
    exact Or.inl ⟨leftLift T U x hx, wedgeιLeft_leftLift T U x hx⟩
  · rcases wedge_bead_cases T U b with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have hx : ∀ i, ((wedge T U).inclusion.app _ x i).val ≤ T.len := by
        intro i
        have hr := (Finset.mem_Icc.mp (h i)).2
        change ((wedge T U).inclusion.app _ x i).val ≤ c.right.val at hr
        exact hr.trans (Nat.le_of_lt_succ c.right.isLt)
      exact Or.inl ⟨leftLift T U x hx, wedgeιLeft_leftLift T U x hx⟩
    · have hx : ∀ i, T.len ≤ ((wedge T U).inclusion.app _ x i).val := by
        intro i
        have hl := (Finset.mem_Icc.mp (h i)).1
        change T.len + c.left.val ≤ ((wedge T U).inclusion.app _ x i).val at hl
        omega
      exact Or.inr ⟨rightLift T U x hx, wedgeιRight_rightLift T U x hx⟩

end

end DaggerChosenRigidificationNecklace.NecklaceCode
