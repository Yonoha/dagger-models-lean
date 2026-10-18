import RawIsoTriangleCells
import SSetOperatorMapValues

/-! The ten actual endpoint and face equations for every chosen inverse-triangle datum. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerInverseTriangleCellFamily
open DaggerRawIsoTriangleCells DaggerSSetOperatorMapValues
universe u
namespace DaggerIsoTriangleFiniteEquations

inductive EquationKind where
  | forwardSrc | forwardTgt | backwardSrc | backwardTgt
  | left2 | left0 | left1 | right2 | right0 | right1
  deriving DecidableEq, Fintype

def EquationKind.degree (k : EquationKind) : ℕ :=
  match k with
  | .forwardSrc => 0
  | .forwardTgt => 0
  | .backwardSrc => 0
  | .backwardTgt => 0
  | .left2 => 1
  | .left0 => 1
  | .left1 => 1
  | .right2 => 1
  | .right0 => 1
  | .right1 => 1

variable (X : SSet.{u}) (s : ∀ k : Kind, X.obj (op ⦋k.degree⦌))

def lhs (k : EquationKind) : X.obj (op ⦋k.degree⦌) :=
  match k with
  | .forwardSrc => X.δ 1 (s .forward)
  | .forwardTgt => X.δ 0 (s .forward)
  | .backwardSrc => X.δ 1 (s .backward)
  | .backwardTgt => X.δ 0 (s .backward)
  | .left2 => X.δ 2 (s .leftTriangle)
  | .left0 => X.δ 0 (s .leftTriangle)
  | .left1 => X.δ 1 (s .leftTriangle)
  | .right2 => X.δ 2 (s .rightTriangle)
  | .right0 => X.δ 0 (s .rightTriangle)
  | .right1 => X.δ 1 (s .rightTriangle)

def rhs (x y : X.obj (op ⦋0⦌)) (k : EquationKind) : X.obj (op ⦋k.degree⦌) :=
  match k with
  | .forwardSrc => x
  | .forwardTgt => y
  | .backwardSrc => y
  | .backwardTgt => x
  | .left2 => s .forward
  | .left0 => s .backward
  | .left1 => X.σ 0 x
  | .right2 => s .backward
  | .right0 => s .forward
  | .right1 => X.σ 0 y

def build (x y : X.obj (op ⦋0⦌)) (h : ∀ k, lhs X s k = rhs X s x y k) :
    IsoTriangles X ((SSet.hoFunctor.obj.equiv X).symm x)
      ((SSet.hoFunctor.obj.equiv X).symm y) where
  forward := SSet.Edge.mk (s .forward)
    (by simpa only [Equiv.apply_symm_apply] using h .forwardSrc)
    (by simpa only [Equiv.apply_symm_apply] using h .forwardTgt)
  backward := SSet.Edge.mk (s .backward)
    (by simpa only [Equiv.apply_symm_apply] using h .backwardSrc)
    (by simpa only [Equiv.apply_symm_apply] using h .backwardTgt)
  leftTriangle := SSet.Edge.CompStruct.mk (s .leftTriangle) (h .left2) (h .left0)
    (by simpa only [SSet.Edge.id_edge, Equiv.apply_symm_apply] using h .left1)
  rightTriangle := SSet.Edge.CompStruct.mk (s .rightTriangle) (h .right2) (h .right0)
    (by simpa only [SSet.Edge.id_edge, Equiv.apply_symm_apply] using h .right1)

theorem cell_build (x y : X.obj (op ⦋0⦌)) (h : ∀ k, lhs X s k = rhs X s x y k) (k : Kind) :
    cell (build X s x y h) k = s k := by cases k <;> rfl

theorem lhs_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (s : ∀ k : Kind, X.obj (op ⦋k.degree⦌)) (k : EquationKind) :
    f.app (op ⦋k.degree⦌) (lhs X s k) =
      lhs Y (fun i ↦ f.app (op ⦋i.degree⦌) (s i)) k := by
  cases k <;> exact map_face f _ _

theorem rhs_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (s : ∀ k : Kind, X.obj (op ⦋k.degree⦌)) (x y : X.obj (op ⦋0⦌)) (k : EquationKind) :
    f.app (op ⦋k.degree⦌) (rhs X s x y k) =
      rhs Y (fun i ↦ f.app (op ⦋i.degree⦌) (s i))
        (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) k := by
  cases k <;> first | rfl | exact map_degeneracy f 0 _

theorem original_equations {x y : SSet.hoFunctor.obj X} (d : IsoTriangles X x y) :
    ∀ k, lhs X (cell d) k =
      rhs X (cell d) (SSet.hoFunctor.obj.equiv X x) (SSet.hoFunctor.obj.equiv X y) k := by
  intro k
  cases k
  · exact d.forward.src_eq
  · exact d.forward.tgt_eq
  · exact d.backward.src_eq
  · exact d.backward.tgt_eq
  · exact d.leftTriangle.d₂
  · exact d.leftTriangle.d₀
  · simpa only [SSet.Edge.id_edge] using d.leftTriangle.d₁
  · exact d.rightTriangle.d₂
  · exact d.rightTriangle.d₀
  · simpa only [SSet.Edge.id_edge] using d.rightTriangle.d₁

end DaggerIsoTriangleFiniteEquations
