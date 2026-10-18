import DaggerModels.RigidificationVertices
import SimplicialIsoHoms

/-!
# The actual directed Hom in the rigidification of the one-simplex

The two endpoints come from the original vertex equivalence.  The target
mapping object is Mathlib's nerve of the path category from `0` to `1` in
the actual lifted finite order, whose only object is the full interval.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory

universe u

namespace DaggerModels.OrdinaryRigidification.DirectedIntervalHom

noncomputable section

private abbrev IntervalOrder := ULift.{u} (Fin 2)

/-- The first object of the selected simplicial thickening of `Δ[1]`. -/
def thickZero : SimplicialThickening IntervalOrder :=
  .mk ⟨(0 : Fin 2)⟩

/-- The last object of the selected simplicial thickening of `Δ[1]`. -/
def thickOne : SimplicialThickening IntervalOrder :=
  .mk ⟨(1 : Fin 2)⟩

/-- The actual directed path category has one object: the full interval. -/
instance pathSubsingleton : Subsingleton (thickZero.{u} ⟶ thickOne.{u}) := by
  constructor
  intro p q
  apply SimplicialThickening.Path.ext
  ext z
  constructor
  · intro _
    cases z with
    | up k =>
      fin_cases k
      · exact q.left
      · exact q.right
  · intro _
    cases z with
    | up k =>
      fin_cases k
      · exact p.left
      · exact p.right

/-- The full interval, viewed as a genuine directed path. -/
def fullPath : thickZero.{u} ⟶ thickOne.{u} where
  I := Set.univ
  left := Set.mem_univ _
  right := Set.mem_univ _
  left_le k _ := by
    cases k with
    | up j => fin_cases j <;> decide
  le_right k _ := by
    cases k with
    | up j => fin_cases j <;> decide

/-- Its actual path-category nerve is terminal in simplicial sets. -/
def pathNerveIsTerminal :
    CategoryTheory.Limits.IsTerminal (nerve (thickZero.{u} ⟶ thickOne.{u})) := by
  let P := thickZero.{u} ⟶ thickOne.{u}
  letI : Subsingleton P := pathSubsingleton.{u}
  have hdegree (q : SimplexCategoryᵒᵖ) :
      Subsingleton ((nerve P).obj q) := by
    constructor
    intro f g
    exact CategoryTheory.Functor.ext (fun _ => Subsingleton.elim _ _)
      (fun _ _ _ => by
        apply InducedCategory.hom_ext
        exact Subsingleton.elim _ _)
  let point : (nerve P).obj (op ⦋0⦌) := (Functor.const _).obj fullPath
  refine CategoryTheory.Limits.IsTerminal.ofUniqueHom (fun X => SSet.const point) ?_
  intro X f
  ext q x
  letI : Subsingleton ((nerve P).obj q) := hdegree q
  exact Subsingleton.elim _ _

/-- The native thickening Hom is exactly the terminal simplicial set. -/
def thickHomIso :
    (thickZero.{u} ⟶[SSet.{u}] thickOne.{u}) ≅ (Δ[0] : SSet.{u}) := by
  change nerve (thickZero.{u} ⟶ thickOne.{u}) ≅ (Δ[0] : SSet.{u})
  exact pathNerveIsTerminal.{u}.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

/-- The first actual vertex of the original standard one-simplex. -/
def vertexZero : (Δ[1] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm 0

/-- The last actual vertex of the original standard one-simplex. -/
def vertexOne : (Δ[1] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm 1

private def simplexIso :
    (rigidification.obj (Δ[1] : SSet.{u})) ≅ simplexThickening.{u} ⦋1⦌ :=
  rigidificationSimplexIso.{u}.app ⦋1⦌

/-- The chosen simplex isomorphism takes the original first vertex to `0`. -/
theorem simplexIso_zero :
    simplexIso.{u}.hom.obj
      (RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexZero.{u}) =
        thickZero.{u} := by
  have hp : RigidificationVertices.representableVerticesEquiv.{u} ⦋1⦌
      vertexZero.{u} = thickZero.{u} := rfl
  have hunit := RigidificationVertices.canonicalVertex_simplex.{u}
    ⦋1⦌ vertexZero.{u}
  have hpre : RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexZero.{u} =
      simplexIso.{u}.inv.obj thickZero.{u} := by
    rw [hp] at hunit
    exact hunit
  rw [hpre]
  have h := congrArg (fun F : simplexThickening.{u} ⦋1⦌ ⟶
      simplexThickening.{u} ⦋1⦌ => F.obj thickZero.{u})
        simplexIso.{u}.inv_hom_id
  exact h

/-- The chosen simplex isomorphism takes the original last vertex to `1`. -/
theorem simplexIso_one :
    simplexIso.{u}.hom.obj
      (RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexOne.{u}) =
        thickOne.{u} := by
  have hp : RigidificationVertices.representableVerticesEquiv.{u} ⦋1⦌
      vertexOne.{u} = thickOne.{u} := rfl
  have hunit := RigidificationVertices.canonicalVertex_simplex.{u}
    ⦋1⦌ vertexOne.{u}
  have hpre : RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexOne.{u} =
      simplexIso.{u}.inv.obj thickOne.{u} := by
    rw [hp] at hunit
    exact hunit
  rw [hpre]
  have h := congrArg (fun F : simplexThickening.{u} ⦋1⦌ ⟶
      simplexThickening.{u} ⦋1⦌ => F.obj thickOne.{u})
        simplexIso.{u}.inv_hom_id
  exact h

/-- The original full Hom of `C Δ[1]`, at its actual directed endpoints, is `Δ[0]`. -/
def directedHomIso :
    (RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexZero.{u} ⟶[SSet.{u}]
      RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexOne.{u}) ≅
        (Δ[0] : SSet.{u}) := by
  let e := DaggerSimplicialIsoHoms.homIso simplexIso.{u}
    (RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexZero.{u})
    (RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexOne.{u})
  have h : (simplexIso.{u}.hom.obj
      (RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexZero.{u})
        ⟶[SSet.{u}] simplexIso.{u}.hom.obj
      (RigidificationVertices.vertexEquiv (Δ[1] : SSet.{u}) vertexOne.{u})) =
        (thickZero.{u} ⟶[SSet.{u}] thickOne.{u}) := by
    rw [simplexIso_zero, simplexIso_one]
  exact e ≪≫ eqToIso h ≪≫ thickHomIso.{u}

end

end DaggerModels.OrdinaryRigidification.DirectedIntervalHom
