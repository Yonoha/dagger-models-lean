import DaggerModels.RigidificationVertices
import SimplicialIsoHoms

/-!
# The actual original Hom of the zero-simplex

The single vertex of `Δ[0]` gives the only object of the selected
simplicial thickening. Its path category and hence its original enriched
Hom are terminal.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory
open DaggerModels.OrdinaryRigidification

universe u

namespace DaggerOriginalRigidificationZeroHom

noncomputable section

private abbrev ZeroOrder := ULift.{u} (Fin 1)

/-- The literal only object of the zero-simplex thickening. -/
def thickPoint : SimplicialThickening ZeroOrder := .mk ⟨(0 : Fin 1)⟩

/-- Its path category has at most one arrow. -/
instance pathSubsingleton : Subsingleton (thickPoint.{u} ⟶ thickPoint.{u}) := by
  constructor
  intro p q
  apply SimplicialThickening.Path.ext
  ext z
  constructor
  · intro _
    cases z with
    | up k =>
      fin_cases k
      exact q.left
  · intro _
    cases z with
    | up k =>
      fin_cases k
      exact p.left

/-- The identity path supplies an object of that path category. -/
def pointPath : thickPoint.{u} ⟶ thickPoint.{u} := 𝟙 thickPoint.{u}

/-- The actual path-category nerve is terminal. -/
def pathNerveIsTerminal :
    CategoryTheory.Limits.IsTerminal (nerve (thickPoint.{u} ⟶ thickPoint.{u})) := by
  let P := thickPoint.{u} ⟶ thickPoint.{u}
  letI : Subsingleton P := pathSubsingleton.{u}
  have hdegree (q : SimplexCategoryᵒᵖ) :
      Subsingleton ((nerve P).obj q) := by
    constructor
    intro f g
    exact CategoryTheory.Functor.ext (fun _ => Subsingleton.elim _ _)
      (fun _ _ _ => by
        apply InducedCategory.hom_ext
        exact Subsingleton.elim _ _)
  let point : (nerve P).obj (op ⦋0⦌) := (Functor.const _).obj pointPath.{u}
  refine CategoryTheory.Limits.IsTerminal.ofUniqueHom (fun X => SSet.const point) ?_
  intro X f
  apply NatTrans.ext
  funext q x
  letI : Subsingleton ((nerve P).obj q) := hdegree q
  exact @Subsingleton.elim ((nerve P).obj q) (hdegree q) _ _

/-- The only thickening Hom is isomorphic to the tensor unit. -/
def thickHomIso :
    (thickPoint.{u} ⟶[SSet.{u}] thickPoint.{u}) ≅ (Δ[0] : SSet.{u}) := by
  change nerve (thickPoint.{u} ⟶ thickPoint.{u}) ≅ (Δ[0] : SSet.{u})
  exact pathNerveIsTerminal.{u}.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

/-- The literal only vertex of the original zero-simplex. -/
def vertex : (Δ[0] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)

private def simplexIso :
    (rigidification.obj (Δ[0] : SSet.{u})) ≅ simplexThickening.{u} ⦋0⦌ :=
  rigidificationSimplexIso.{u}.app ⦋0⦌

/-- The chosen object map takes the actual zero vertex to the unique object. -/
theorem simplexIso_vertex :
    simplexIso.{u}.hom.obj
      (RigidificationVertices.vertexEquiv
        (Δ[0] : SSet.{u}) vertex.{u}) = thickPoint.{u} := by
  have hp : RigidificationVertices.representableVerticesEquiv.{u}
      ⦋0⦌ vertex.{u} = thickPoint.{u} := rfl
  have hunit := RigidificationVertices.canonicalVertex_simplex.{u}
    ⦋0⦌ vertex.{u}
  have hpre : RigidificationVertices.vertexEquiv
      (Δ[0] : SSet.{u}) vertex.{u} = simplexIso.{u}.inv.obj thickPoint.{u} := by
    rw [hp] at hunit
    exact hunit
  rw [hpre]
  have h := congrArg (fun F : simplexThickening.{u} ⦋0⦌ ⟶
      simplexThickening.{u} ⦋0⦌ => F.obj thickPoint.{u}) simplexIso.{u}.inv_hom_id
  exact h

/-- The Hom of the actual original `C Δ[0]` is the terminal simplicial set. -/
def originalHomIso :
    (RigidificationVertices.vertexEquiv
      (Δ[0] : SSet.{u}) vertex.{u} ⟶[SSet.{u}]
        RigidificationVertices.vertexEquiv
          (Δ[0] : SSet.{u}) vertex.{u}) ≅ (Δ[0] : SSet.{u}) := by
  let e := DaggerSimplicialIsoHoms.homIso simplexIso.{u}
    (RigidificationVertices.vertexEquiv
      (Δ[0] : SSet.{u}) vertex.{u})
    (RigidificationVertices.vertexEquiv
      (Δ[0] : SSet.{u}) vertex.{u})
  have h : (simplexIso.{u}.hom.obj
      (RigidificationVertices.vertexEquiv
        (Δ[0] : SSet.{u}) vertex.{u}) ⟶[SSet.{u}]
      simplexIso.{u}.hom.obj
        (RigidificationVertices.vertexEquiv
          (Δ[0] : SSet.{u}) vertex.{u})) =
        (thickPoint.{u} ⟶[SSet.{u}] thickPoint.{u}) := by
    rw [simplexIso_vertex]
  exact e ≪≫ eqToIso h ≪≫ thickHomIso.{u}

/-- The actual original zero-simplex Hom has unique maps into it. -/
def originalHomIsTerminal :
    CategoryTheory.Limits.IsTerminal
      (RigidificationVertices.vertexEquiv
        (Δ[0] : SSet.{u}) vertex.{u} ⟶[SSet.{u}]
          RigidificationVertices.vertexEquiv
            (Δ[0] : SSet.{u}) vertex.{u}) :=
  CategoryTheory.Limits.IsTerminal.ofIso
    SSet.stdSimplex.isTerminalObj₀ originalHomIso.{u}.symm

end

end DaggerOriginalRigidificationZeroHom
