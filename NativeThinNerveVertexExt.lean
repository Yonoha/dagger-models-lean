import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! Maps into an actual thin-category nerve are determined by their entire vertex map. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
universe u
namespace DaggerNativeThinNerveVertexExt

theorem nerveMap_ext_of_vertices (T : Type u) [Category.{u} T] [Quiver.IsThin T]
    {X : SSet.{u}} (f g : X ⟶ nerve T)
    (h : ∀ x : X _⦋0⦌, f.app (op ⦋0⦌) x = g.app (op ⦋0⦌) x) : f = g := by
  apply NatTrans.ext
  funext n s
  apply nerve.ext_of_isThin
  funext j
  let α := ((⦋0⦌ : SimplexCategory).const n.unop j).op
  have hf := congrFun (f.naturality α) s
  have hg := congrFun (g.naturality α) s
  exact congrArg nerveEquiv (hf.symm.trans ((h (X.map α s)).trans hg))

end DaggerNativeThinNerveVertexExt
