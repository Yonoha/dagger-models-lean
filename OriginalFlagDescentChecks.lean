import OriginalFlagFlankedDescent

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification.DescentChecks

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}
variable (p q r : FlankedDegree X a b n)
variable (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r)

include hq in
theorem original_full_unique : ∃! l : r ⟶ q, g ≫ l = f :=
  flankedDegree_descent_unique p q r hq f g

theorem original_whole_map :
    g.hom.val.hom.map ≫ (flankedDegreeDescent p q r hq f g).hom.val.hom.map =
      f.hom.val.hom.map :=
  flankedDegreeDescent_whole p q r hq f g

theorem original_over_X :
    (flankedDegreeDescent p q r hq f g).hom.val.hom.map ≫ q.obj.1.map = r.obj.1.map :=
  flankedDegreeDescent_triangle p q r hq f g

theorem original_both_endpoints :
    (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app (op ⦋0⦌)
        r.obj.1.code.first = q.obj.1.code.first ∧
      (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app (op ⦋0⦌)
        r.obj.1.code.last = q.obj.1.code.last :=
  ⟨flankedDegreeDescent_first p q r hq f g, flankedDegreeDescent_last p q r hq f g⟩

theorem original_every_flag_image (i : Fin (n + 1)) :
    mapVertices (flankedDegreeDescent p q r hq f g).hom.val.hom.map '' r.obj.2.chain i =
      q.obj.2.chain i :=
  flankedDegreeDescent_flag_image p q r hq f g i

theorem original_every_operator {s t : SimplexCategoryᵒᵖ} (α : s ⟶ t) :
    r.obj.1.code.toSSet.map α ≫ (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app t =
      (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app s ≫ q.obj.1.code.toSSet.map α :=
  (flankedDegreeDescent p q r hq f g).hom.val.hom.map.naturality α

theorem original_vertex_factor (v : Vertices.{u} p.obj.1.code) :
    mapVertices (flankedDegreeDescent p q r hq f g).hom.val.hom.map
      (mapVertices g.hom.val.hom.map v) = mapVertices f.hom.val.hom.map v := by
  have h := congrArg (mapVertices (T := p.obj.1.code) (U := q.obj.1.code))
    (flankedDegreeDescent_whole p q r hq f g)
  rw [mapVertices_comp] at h
  exact congrFun h v

theorem zero_flag_diagonal {X : SSet.{u}} (a : X.obj (op ⦋0⦌))
    (p q r : FlankedDegree X a a 0) (hq : TotallyNondegenerate X a a 0 q.obj)
    (f : p ⟶ q) (g : p ⟶ r) : ∃! l : r ⟶ q, g ≫ l = f :=
  flankedDegree_descent_unique p q r hq f g

end

end DaggerOriginalFlagFlankification.DescentChecks
