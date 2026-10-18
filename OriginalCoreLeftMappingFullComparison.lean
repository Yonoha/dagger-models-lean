import OriginalLeftMappingCoreSubcomplex

/-!
# The actual ordinary-core mapping space is the original full subcomplex

The mapping-space map induced by the original core inclusion factors through
literal original-core simplex membership. Moving that same membership proof
between the nested native subtype objects gives a degreewise equivalence,
hence a simplicial isomorphism. The proved full-subcomplex equality identifies
this actual original mapping space with the original invertible-edge vertex
subcomplex, with the exact inclusion map retained.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalLeftMappingCoreSubcomplex DaggerOriginalFullVertexSubcomplex

universe u

namespace DaggerOriginalCoreLeftMappingFullComparison

noncomputable section

variable (X : SSet.{u})
variable (a b : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌))

/-- The actual original mapping-space map induced by the original ordinary-core inclusion. -/
def coreMappingInclusion :
    leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b ⟶
      leftMappingSpace X a.val b.val :=
  leftMappingMap (ordinaryCoreCandidate X).ι a b

/-- The exact core-inclusion map with its underlying joined simplex core-membership proof. -/
def coreMappingToCoreSimplex :
    leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b ⟶
      (coreSimplexSubcomplex X a.val b.val : SSet.{u}) where
  app n v := ⟨(coreMappingInclusion X a b).app n v, v.val.val.property⟩
  naturality _ _ φ := by
    funext v
    apply Subtype.ext
    exact congrFun ((coreMappingInclusion X a b).naturality φ) v

/-- The actual factorization retains precisely the same original ambient mapping-space arrow. -/
theorem coreMappingToCoreSimplex_ι :
    coreMappingToCoreSimplex X a b ≫ (coreSimplexSubcomplex X a.val b.val).ι =
      coreMappingInclusion X a b := rfl

/-- The actual simplices differ only by placement of the same original-core membership proof. -/
def coreSimplexEquiv (n : SimplexCategoryᵒᵖ) :
    (leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b).obj n ≃
      (coreSimplexSubcomplex X a.val b.val : SSet.{u}).obj n where
  toFun := (coreMappingToCoreSimplex X a b).app n
  invFun s := by
    let r : (ordinaryCoreCandidate X : SSet.{u}).obj
        (op ((ordinalJoinLeft ⦋0⦌).obj n.unop)) := ⟨s.val.val.val, s.property⟩
    let t : (simplexCoslice ⦋0⦌ (ordinaryCoreCandidate X : SSet.{u}) a).obj n :=
      ⟨r, by apply Subtype.ext; exact s.val.val.property⟩
    refine ⟨t, (SSet.Subcomplex.mem_fiber_obj_iff
      (cosliceProjection ⦋0⦌ (ordinaryCoreCandidate X : SSet.{u}) a) b t).mpr ?_⟩
    apply Subtype.ext
    exact (SSet.Subcomplex.mem_fiber_obj_iff
      (cosliceProjection ⦋0⦌ X a.val) b.val s.val.val).mp s.val.property
  left_inv v := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv s := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl

/-- The actual factorization is a native simplicial isomorphism in arbitrary universe. -/
theorem coreMappingToCoreSimplex_isIso : IsIso (coreMappingToCoreSimplex X a b) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro n
  exact (isIso_iff_bijective _).mpr (coreSimplexEquiv X a b n).bijective

/-- Transport of a subcomplex equality retains the literal original inclusion. -/
theorem subcomplex_eqToIso_hom_ι {K : SSet.{u}} {A B : K.Subcomplex} (h : A = B) :
    (eqToIso (congrArg (fun C : K.Subcomplex ↦ (C : SSet.{u})) h)).hom ≫ B.ι = A.ι := by
  cases h
  simp

/-- The actual original-core mapping space is the full original subcomplex on invertible edges.
-/
def coreMappingFullIso :
    leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b ≅
      (fullVertexSubcomplex (leftMappingSpace X a.val b.val)
        (equivalenceVertexSet X a.val b.val) : SSet.{u}) := by
  haveI := coreMappingToCoreSimplex_isIso X a b
  exact asIso (coreMappingToCoreSimplex X a b) ≪≫
    eqToIso (congrArg (fun A : (leftMappingSpace X a.val b.val).Subcomplex ↦ (A : SSet.{u}))
      (coreSimplexSubcomplex_eq_fullVertexSubcomplex X a.val b.val))

/-- This isomorphism followed by the full-subcomplex inclusion is exactly the original map. -/
theorem coreMappingFullIso_hom_ι :
    (coreMappingFullIso X a b).hom ≫
        (fullVertexSubcomplex (leftMappingSpace X a.val b.val)
          (equivalenceVertexSet X a.val b.val)).ι = coreMappingInclusion X a b := by
  change (coreMappingToCoreSimplex X a b ≫
    (eqToIso (congrArg (fun A : (leftMappingSpace X a.val b.val).Subcomplex ↦ (A : SSet.{u}))
      (coreSimplexSubcomplex_eq_fullVertexSubcomplex X a.val b.val))).hom) ≫ _ = _
  rw [Category.assoc, subcomplex_eqToIso_hom_ι
    (coreSimplexSubcomplex_eq_fullVertexSubcomplex X a.val b.val),
    coreMappingToCoreSimplex_ι]

end

end DaggerOriginalCoreLeftMappingFullComparison
