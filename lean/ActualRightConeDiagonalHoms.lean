import ActualRightConePointNecklaceSimple
import OriginalSimpleOriginalHomIso
import OriginalRigidificationDirectedIntervalHomNativeIsoReconciled

/-! Both diagonal Homs of the literal original rigidified right cone are terminal. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory
open DaggerModels.OrdinaryRigidification DaggerOriginalCounitRightCone
open DaggerOriginalProductGadget DaggerActualRightConePointNecklaceSimple
universe u

namespace DaggerActualRightConeDiagonalHoms
noncomputable section

/-- The native ordered-path description makes every rigidified simplex diagonal terminal. -/
def simplex_diagonal_isTerminal (n : ℕ)
    (a : (rigidification.{u}.obj (Δ[n] : SSet.{u})).Obj) :
    IsTerminal (a ⟶[SSet.{u}] a) := by
  let e := rigidificationSimplexIso.{u}.app ⦋n⦌
  let b : SimplicialThickening (ULift.{u} (Fin (n + 1))) := e.hom.obj a
  let P := b ⟶ b
  have hP : Subsingleton P := by
    constructor
    intro p q
    apply SimplicialThickening.Path.ext
    ext z
    constructor
    · intro hz
      have he : z = b.as := le_antisymm (p.le_right z hz) (p.left_le z hz)
      exact he ▸ q.left
    · intro hz
      have he : z = b.as := le_antisymm (q.le_right z hz) (q.left_le z hz)
      exact he ▸ p.left
  have hdegree (q : SimplexCategoryᵒᵖ) : Subsingleton ((nerve P).obj q) := by
    constructor
    intro f g
    exact CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)
      (fun _ _ _ ↦ by
        apply InducedCategory.hom_ext
        exact Subsingleton.elim _ _)
  let point : (nerve P).obj (op ⦋0⦌) := (Functor.const _).obj (𝟙 b)
  have ht : IsTerminal (nerve P) := by
    refine IsTerminal.ofUniqueHom (fun X ↦ SSet.const point) ?_
    intro X f
    ext q x
    exact (hdegree q).elim _ _
  exact ht.ofIso (DaggerSimplicialIsoHoms.homIso e a a).symm

private theorem point_mono {X : SSet.{u}} (j : (Δ[0] : SSet.{u}) ⟶ X) : Mono j := by
  constructor
  intro Z f g _
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext f g

/-- The original point inclusion induces this full enriched Hom isomorphism. -/
def alphaHomIso (n : ℕ) :
    (RigidificationVertices.vertexEquiv (Δ[0] : SSet.{u})
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ⟶[SSet.{u}]
      RigidificationVertices.vertexEquiv (Δ[0] : SSet.{u})
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≅
      (alphaObj.{u} n ⟶[SSet.{u}] alphaObj.{u} n) := by
  have : Mono (alphaMap.{u} n) := point_mono _
  exact simpleOriginalHomIso (alphaMap n) (alpha_necklaceSimple n)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))

/-- The actual tip inclusion has the same property. -/
def omegaHomIso (n : ℕ) :
    (RigidificationVertices.vertexEquiv (Δ[0] : SSet.{u})
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ⟶[SSet.{u}]
      RigidificationVertices.vertexEquiv (Δ[0] : SSet.{u})
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≅
      (omegaObj.{u} n ⟶[SSet.{u}] omegaObj.{u} n) := by
  have : Mono (omegaMap.{u} n) := point_mono _
  exact simpleOriginalHomIso (omegaMap n) (omega_necklaceSimple n)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))

def alpha_isTerminal (n : ℕ) : IsTerminal (alphaObj.{u} n ⟶[SSet.{u}] alphaObj.{u} n) :=
  (simplex_diagonal_isTerminal 0 _).ofIso (alphaHomIso n)

def omega_isTerminal (n : ℕ) : IsTerminal (omegaObj.{u} n ⟶[SSet.{u}] omegaObj.{u} n) :=
  (simplex_diagonal_isTerminal 0 _).ofIso (omegaHomIso n)

end
end DaggerActualRightConeDiagonalHoms
