import OriginalFlagFlankedDescent

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

open DaggerChosenRigidificationNecklace NecklaceCode DaggerOriginalFlagFlankification

noncomputable section

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p q r : FlankedDegree X a b n)
    (_hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r),
    ∃! l : r ⟶ q, g ≫ l = f := by
  intro X a b n p q r hq f g
  exact flankedDegree_descent_unique p q r hq f g

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r),
    g.hom.val.hom.map ≫ (flankedDegreeDescent p q r hq f g).hom.val.hom.map =
      f.hom.val.hom.map := by
  intros
  exact flankedDegreeDescent_whole _ _ _ _ _ _

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r),
    (flankedDegreeDescent p q r hq f g).hom.val.hom.map ≫ q.obj.1.map = r.obj.1.map := by
  intros
  exact flankedDegreeDescent_triangle _ _ _ _ _ _

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r)
    (i : Fin (n + 1)),
    mapVertices (flankedDegreeDescent p q r hq f g).hom.val.hom.map '' r.obj.2.chain i =
      q.obj.2.chain i := by
  intros
  exact flankedDegreeDescent_flag_image _ _ _ _ _ _ _

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r),
    (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app (op ⦋0⦌)
        r.obj.1.code.first = q.obj.1.code.first ∧
      (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app (op ⦋0⦌)
        r.obj.1.code.last = q.obj.1.code.last := by
  intros
  exact ⟨flankedDegreeDescent_first _ _ _ _ _ _, flankedDegreeDescent_last _ _ _ _ _ _⟩

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (p q r : FlankedDegree X a b n)
    (hq : TotallyNondegenerate X a b n q.obj) (f : p ⟶ q) (g : p ⟶ r)
    (s t : SimplexCategoryᵒᵖ) (α : s ⟶ t),
    r.obj.1.code.toSSet.map α ≫ (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app t =
      (flankedDegreeDescent p q r hq f g).hom.val.hom.map.app s ≫ q.obj.1.code.toSSet.map α := by
  intros
  exact (flankedDegreeDescent _ _ _ _ _ _).hom.val.hom.map.naturality _

example : ∀ (X : SSet.{0}) (a : X.obj (op ⦋0⦌))
    (p q r : FlankedDegree X a a 0)
    (_hq : TotallyNondegenerate X a a 0 q.obj) (f : p ⟶ q) (g : p ⟶ r),
    ∃! l : r ⟶ q, g ≫ l = f := by
  intro X a p q r hq f g
  exact flankedDegree_descent_unique p q r hq f g

end
