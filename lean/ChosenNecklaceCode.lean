import ChosenRigidificationSimplexColimit
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

/-- Finite ordered vertices and all joints, including the two outer vertices. -/
structure NecklaceCode where
  len : ℕ
  joints : Finset (Fin (len + 1))
  first_mem : (0 : Fin (len + 1)) ∈ joints
  last_mem : Fin.last len ∈ joints

namespace NecklaceCode

noncomputable section

variable (T : NecklaceCode)

abbrev Vertices := ULift.{u} (Fin (T.len + 1))

def point : NecklaceCode where
  len := 0
  joints := {0}
  first_mem := by simp
  last_mem := by simp

/-- A positive bead is exactly a consecutive pair of original joints. -/
structure Bead where
  left : Fin (T.len + 1)
  right : Fin (T.len + 1)
  left_mem : left ∈ T.joints
  right_mem : right ∈ T.joints
  lt : left < right
  no_joint : ∀ v ∈ T.joints, left < v → v < right → False

namespace Bead

variable {T} (b : T.Bead)

def interval : Finset (Fin (T.len + 1)) := Finset.Icc b.left b.right

theorem left_mem_interval : b.left ∈ b.interval := Finset.mem_Icc.mpr ⟨le_rfl, b.lt.le⟩

theorem right_mem_interval : b.right ∈ b.interval := Finset.mem_Icc.mpr ⟨b.lt.le, le_rfl⟩

def length : ℕ := b.interval.card - 1

theorem card_interval : b.interval.card = b.length + 1 := by
  have h : 0 < b.interval.card := Finset.card_pos.mpr ⟨_, b.left_mem_interval⟩
  dsimp [length]
  omega

def face : (Δ[T.len] : SSet.{u}).Subcomplex := SSet.stdSimplex.face b.interval

/-- The actual standard-simplex face iso, retaining all simplex operators. -/
def faceIso : (Δ[b.length] : SSet.{u}) ≅ b.face.toSSet :=
  SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy b.interval b.length
      (b.interval.orderIsoOfFin b.card_interval))

include b in
theorem len_ne_zero : T.len ≠ 0 := by
  intro h
  have hh := b.lt
  have hl := b.left.isLt
  have hr := b.right.isLt
  simp only [Fin.lt_def] at hh
  omega

end Bead

/-- The literal union of positive bead faces, with its initial point included. -/
def complex : (Δ[T.len] : SSet.{u}).Subcomplex :=
  SSet.stdSimplex.face {0} ⊔ ⨆ b : T.Bead, b.face

/-- Zero length is the original point. All positive lengths use the actual union. -/
def toSSet : SSet.{u} := if T.len = 0 then Δ[0] else T.complex.toSSet

@[simp] theorem point_toSSet : toSSet.{u} point = Δ[0] := rfl

def beadι (b : T.Bead) : (Bead.face.{u} b).toSSet ⟶ T.toSSet :=
  SSet.Subcomplex.homOfLE (show b.face ≤ T.complex from
    le_sup_of_le_right (le_iSup (fun c : T.Bead ↦ c.face) b)) ≫
    eqToHom (by simp [toSSet, b.len_ne_zero])

/-- Every original bead leg starts at its actual standard simplex. -/
def beadSimplex (b : T.Bead) : (Δ[b.length] : SSet.{u}) ⟶ T.toSSet :=
  b.faceIso.hom ≫ T.beadι b

end

end NecklaceCode

end DaggerChosenRigidificationNecklace
