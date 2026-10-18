import ActualRigidificationProductHomProjection
import OriginalProductBeadFlagCollapseReconciledRecovered

/-! Every ordered-endpoint path category in the original simplex thickening
has contractible nerve. -/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalProductGadget DaggerOriginalFlagFlankification DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualThickeningPathContractibility

noncomputable section
variable {J : Type u} [LinearOrder J] (i j : J) (hij : i ≤ j)

/-- The shortest path contains exactly the two prescribed endpoints. -/
def shortestPath : SimplicialThickening.Path i j where
  I := {i, j}
  left := by simp
  right := by simp
  left_le k hk := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact le_rfl
    · exact hij
  le_right k hk := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact hij
    · exact le_rfl

/-- The literal collapse to a one-object discrete category. -/
def collapse : SimplicialThickening.Path i j ⥤ Discrete PUnit.{u + 1} :=
  (Functor.const _).obj (Discrete.mk PUnit.unit)

/-- Select the actual shortest path as the center. -/
def center : Discrete PUnit.{u + 1} ⥤ SimplicialThickening.Path i j :=
  (Functor.const _).obj (shortestPath i j hij)

/-- The endpoint inclusions give a natural transformation from the center to every path. -/
def centerToId : collapse i j ⋙ center i j hij ⟶ 𝟭 (SimplicialThickening.Path i j) where
  app p := InducedCategory.homMk (homOfLE (by
    change ({i, j} : Set J) ⊆ p.I
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact p.left
    · exact p.right))
  naturality _ _ _ := by
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

/-- The other composite is naturally the identity on the same one-object category. -/
def collapseToId : center i j hij ⋙ collapse i j ⟶ 𝟭 (Discrete PUnit.{u + 1}) where
  app _ := eqToHom (Subsingleton.elim _ _)
  naturality _ _ _ := Subsingleton.elim _ _

include hij in
/-- The original nerve of the entire path category is weakly contractible. -/
theorem path_point_GW : DaggerSSetGluing.GW
    (pointMap (nerve (SimplicialThickening.Path i j))) := by
  have : WeakEquivalence (nerveMap (collapse i j)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (nerveMap_geometricW (collapse i j) (center i j hij)
        (Relation.EqvGen.rel _ _ ⟨centerToId i j hij⟩)
        (Relation.EqvGen.rel _ _ ⟨collapseToId i j hij⟩))
  have hpoint : nerveMap (collapse i j) ≫ (nerveDiscreteIso PUnit).hom =
      pointMap (nerve (SimplicialThickening.Path i j)) :=
    pointIsTerminal.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).1
  rw [← hpoint]
  infer_instance

end
end DaggerActualThickeningPathContractibility
