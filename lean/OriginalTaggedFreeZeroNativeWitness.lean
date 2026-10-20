import OriginalTaggedReverseFreeCompletion
import DaggerModels.FreeDaggerPushout
import DaggerModels.FreeCofibration
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The literal free-zero witness for the tagged restriction

The free dagger simplicial set on the standard zero-simplex is canonically
terminal. The existing point and pushout proof is reused with native imports only.
Thus the initial-to-point obstruction is the same actual arrow,
up to a specified target isomorphism, as the paper's
`∅ ⟶ freeDagger.obj (Δ[0])`. The failure of normality is also checked
directly on that literal tagged image arrow.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open DaggerModels
open DaggerModels.OriginalTaggedReversePresheafInclusion

universe u

namespace DaggerOriginalTaggedFreeZeroNativeWitness

noncomputable section

private theorem zeroSimplex_subsingleton (q : SimplexCategoryᵒᵖ) :
    Subsingleton ((Δ[0] : SSet.{u}).obj q) := by
  constructor
  intro x y
  apply SSet.stdSimplex.objEquiv.injective
  exact (SimplexCategory.eq_const_to_zero (SSet.stdSimplex.objEquiv x)).trans
    (SimplexCategory.eq_const_to_zero (SSet.stdSimplex.objEquiv y)).symm

/-- The discrete vertices already comprise every simplex of `Δ[0]`. -/
private theorem zero_vertices_inclusion_isIso :
    IsIso (SSetVertices.inclusion (Δ[0] : SSet.{u})) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  constructor
  · intro x y _
    have := zeroSimplex_subsingleton.{u} (op ⦋0⦌)
    exact @Subsingleton.elim ((Δ[0] : SSet.{u}).obj (op ⦋0⦌)) inferInstance x y
  · intro y
    refine ⟨SSet.stdSimplex.obj₀Equiv.symm 0, ?_⟩
    have := zeroSimplex_subsingleton.{u} q
    exact Subsingleton.elim _ _

/-- The first copy in the concrete free-dagger pushout is an isomorphism at zero. -/
private theorem zero_pushout_inl_isIso :
    IsIso (FreeDaggerPushout.inl (Δ[0] : SSet.{u})) := by
  haveI : IsIso (SSetVertices.inclusion (Δ[0] : SSet.{u})) :=
    zero_vertices_inclusion_isIso
  haveI : IsIso (SSetVertices.opInclusion (Δ[0] : SSet.{u})) := by
    rw [← SSetVertices.opIso_hom_op_inclusion]
    infer_instance
  exact (IsPushout.of_hasPushout
    (SSetVertices.inclusion (Δ[0] : SSet.{u}))
    (SSetVertices.opInclusion (Δ[0] : SSet.{u}))).isIso_inl_of_isIso

/-- A dagger simplicial set whose underlying simplicial set is terminal is terminal. -/
private def terminal_of_underlying_terminal (X : DaggerSSet.{u})
    (hX : IsTerminal X.toSSet) : IsTerminal X := by
  let hOp : IsTerminal X.toSSet.op := hX.ofIso (DaggerSSet.daggerIso X)
  exact IsTerminal.ofUniqueHom
    (fun Y ↦
      { hom := hX.from Y.toSSet
        comm := hOp.hom_ext _ _ })
    (by
      intro Y f
      apply DaggerSSet.Hom.ext
      exact hX.hom_ext _ _)

/-- The concrete pushout realization of free dagger completion at `Δ[0]` is terminal. -/
def pushoutZeroIsTerminal : IsTerminal (FreeDaggerPushout.obj (Δ[0] : SSet.{u})) := by
  have : IsIso (FreeDaggerPushout.inl (Δ[0] : SSet.{u})) := zero_pushout_inl_isIso
  exact terminal_of_underlying_terminal _
    (SSet.stdSimplex.isTerminalObj₀.ofIso
      (asIso (FreeDaggerPushout.inl (Δ[0] : SSet.{u}))))

/-- The literal free dagger zero-simplex is the original one-point dagger object. -/
def pointFreeZeroIso : DaggerSSet.point.{u} ≅ freeDagger.obj (Δ[0] : SSet.{u}) :=
  DaggerSSet.pointIsTerminal.uniqueUpToIso pushoutZeroIsTerminal ≪≫
    FreeDaggerPushout.isoFreeDagger.app (Δ[0] : SSet.{u})

/-- The paper's literal initial-to-free-zero arrow. -/
def freeZeroArrow : DaggerSSet.empty.{u} ⟶ freeDagger.obj (Δ[0] : SSet.{u}) :=
  DaggerSSet.emptyIsInitial.to _

/-- The literal arrow is the known point witness transported by the target isomorphism. -/
theorem freeZeroArrow_eq :
    freeZeroArrow.{u} = DaggerSSet.emptyToPoint ≫ pointFreeZeroIso.hom :=
  DaggerSSet.emptyIsInitial.hom_ext _ _

/-- The literal manuscript arrow is in the actual original free-cofibration class. -/
theorem freeZeroArrow_freeCofibration : DaggerSSet.FreeCofibration freeZeroArrow.{u} := by
  rw [freeZeroArrow_eq]
  have hIsoCof : DaggerSSet.FreeCofibration pointFreeZeroIso.{u}.hom := by
    refine ⟨inferInstance, ?_⟩
    intro n _ x _ hmiss
    exfalso
    apply hmiss
    refine ⟨pointFreeZeroIso.inv.hom.app (op ⦋n⦌) x, ?_⟩
    have h := pointFreeZeroIso.{u}.inv_hom_id
    exact congrFun (NatTrans.congr_app
      (congrArg (fun f : freeDagger.obj (Δ[0] : SSet.{u}) ⟶
        freeDagger.obj (Δ[0] : SSet.{u}) ↦ f.hom) h) (op ⦋n⦌)) x
  exact DaggerSSet.FreeCofibration.comp
    DaggerSSet.emptyToPoint_freeCofibration hIsoCof

/-- The actual tagged image of the literal arrow fails normality at its new vertex. -/
theorem restricted_freeZeroArrow_not_normalMono :
    ¬ AntiInvolutiveSSet.NormalMono
      (presheafRoute.{u}.map freeZeroArrow.{u}) := by
  intro h
  let y : (presheafRoute.{u}.obj (freeDagger.obj (Δ[0] : SSet.{u}))).toSSet _⦋0⦌ :=
    pointFreeZeroIso.hom.hom.app (op ⦋0⦌) PUnit.unit
  have hnd : y ∈
      (presheafRoute.{u}.obj (freeDagger.obj (Δ[0] : SSet.{u}))).toSSet.nonDegenerate 0 := by
    simp [SSet.nondegenerate_zero]
  have hmiss : y ∉ Set.range
      ((presheafRoute.{u}.map freeZeroArrow.{u}).hom.app (op ⦋0⦌)) := by
    rintro ⟨x, _⟩
    exact PEmpty.elim x
  have hfixed :
      (presheafRoute.{u}.obj (freeDagger.obj (Δ[0] : SSet.{u}))).daggerSimplex y = y := by
    rw [restrictedDagger]
    exact (freeDagger.obj (Δ[0] : SSet.{u})).dagger_vertex y
  exact h.2 0 y hnd hmiss hfixed

/-- Both claims use the same original free-zero arrow and the actual restriction functor. -/
theorem literal_freeZero_cofibration_not_normal :
    DaggerSSet.FreeCofibration freeZeroArrow.{u} ∧
      ¬ AntiInvolutiveSSet.NormalMono
        (presheafRoute.{u}.map freeZeroArrow.{u}) :=
  ⟨freeZeroArrow_freeCofibration, restricted_freeZeroArrow_not_normalMono⟩

end

end DaggerOriginalTaggedFreeZeroNativeWitness
