import OriginalFlagDescentOver
import OriginalFlagNormalTargetUniqueness

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}

/-- Actual full arrow: only the supplied q is nondegenerate; r is unrestricted. -/
def flankedDegreeDescent (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r) : r ⟶ q :=
  ObjectProperty.homMk
    (CategoryOfElements.homMk (F := flagDegreeDiagram X a b (op ⦋n⦌)) r.obj q.obj
      (flankedDescentOver p.obj.2 q.obj.2 r.obj.2 f.hom.val g.hom.val
        f.hom.property g.hom.property p.property q.property r.property hq)
      (flankedDescentOver_flag p.obj.2 q.obj.2 r.obj.2 f.hom.val g.hom.val
        f.hom.property g.hom.property p.property q.property r.property hq))

theorem flankedDegreeDescent_factor (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r) :
    g ≫ flankedDegreeDescent p q r hq f g = f := by
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  exact flankedDescentOver_factor p.obj.2 q.obj.2 r.obj.2 f.hom.val g.hom.val
    f.hom.property g.hom.property p.property q.property r.property hq

theorem flankedDegreeDescent_whole (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r) :
    g.hom.val.hom.map ≫ (flankedDegreeDescent p q r hq f g).hom.val.hom.map =
      f.hom.val.hom.map :=
  flankedDescentCodeHom_factor p.obj.2 q.obj.2 r.obj.2 f.hom.val g.hom.val
    f.hom.property g.hom.property p.property q.property r.property hq

theorem flankedDegreeDescent_triangle (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r) :
    (flankedDegreeDescent p q r hq f g).hom.val.hom.map ≫ q.obj.1.map = r.obj.1.map :=
  (flankedDegreeDescent p q r hq f g).hom.val.w

theorem flankedDegreeDescent_first (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r) :
    (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app (op ⦋0⦌)
      r.obj.1.code.first = q.obj.1.code.first :=
  (flankedDegreeDescent p q r hq f g).hom.val.hom.first

theorem flankedDegreeDescent_last (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r) :
    (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app (op ⦋0⦌)
      r.obj.1.code.last = q.obj.1.code.last :=
  (flankedDegreeDescent p q r hq f g).hom.val.hom.last

theorem flankedDegreeDescent_flag (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r) :
    NecklaceCode.Flag.map (flankedDegreeDescent p q r hq f g).hom.val.hom r.obj.2 =
      q.obj.2 :=
  (flankedDegreeDescent p q r hq f g).hom.property

theorem flankedDegreeDescent_flag_image (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r)
    (i : Fin (n + 1)) :
    mapVertices (flankedDegreeDescent p q r hq f g).hom.val.hom.map '' r.obj.2.chain i =
      q.obj.2.chain i :=
  congrArg (fun F : Flag.{u} q.obj.1.code n ↦ F.chain i)
    (flankedDegreeDescent_flag p q r hq f g)

/-- D3's unchanged full original target, including actual flags and all arrow fields. -/
theorem flankedDegree_descent_unique (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r) :
    ∃! l : r ⟶ q, g ≫ l = f := by
  refine ⟨flankedDegreeDescent p q r hq f g,
    flankedDegreeDescent_factor p q r hq f g, ?_⟩
  intro l _hl
  exact flankedDegree_hom_unique r q hq l (flankedDegreeDescent p q r hq f g)

end

end DaggerOriginalFlagFlankification
