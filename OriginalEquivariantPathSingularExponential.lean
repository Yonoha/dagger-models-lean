import OriginalEquivariantPathFamilyExponential

/-!
# Singular of original equivariant paths and paths in the original mapping space

The exact compact-parameter equivalence is applied to every original realized standard simplex.
Its original parameter naturality and the native realization-singular adjunction assemble a
simplicial isomorphism. The original EC₂, fixed endpoints, pointwise action, compact-open spaces
and canonical unitary labels are preserved. No homeomorphism of the entire mapping spaces is
asserted, and no extra local compactness assumption on original EC₂ is used.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEquivariantConstantMaps DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalContinuousEndpointCylinderFamilies
open DaggerOriginalEquivariantFixedEndpointPathAction DaggerOriginalEquivariantPathFamilyExponential
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryStrictContinuousPathIso
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalEquivariantPathSingularExponential

noncomputable section

/-- The actual original realized standard simplex is locally compact, by its native isomorphism.
-/
instance realizedSimplex_locallyCompact (n : SimplexCategory) :
    LocallyCompactSpace (SSet.toTop.{u}.obj (SSet.stdSimplex.obj n)) := by
  have : CompactSpace (SimplexCategory.toTop.{u}.obj n) :=
    inferInstanceAs (CompactSpace (ULift (_root_.stdSimplex ℝ (Fin (n.len + 1)))))
  have : T2Space (SimplexCategory.toTop.{u}.obj n) :=
    inferInstanceAs (T2Space (ULift (_root_.stdSimplex ℝ (Fin (n.len + 1)))))
  have : CompactSpace (SSet.toTop.{u}.obj (SSet.stdSimplex.obj n)) :=
    (TopCat.homeoOfIso (SSet.toTopSimplex.{u}.app n)).symm.compactSpace
  have : T2Space (SSet.toTop.{u}.obj (SSet.stdSimplex.obj n)) :=
    (TopCat.homeoOfIso (SSet.toTopSimplex.{u}.app n)).symm.t2Space
  infer_instance

/-- Native simplex Yoneda retains the actual original simplex parameter map. -/
theorem singularYoneda_symm_parameter_naturality {A : SSet.{u}}
    {m n : SimplexCategory} (f : m ⟶ n) (s : A.obj (op n)) :
    SSet.yonedaEquiv.symm (A.map f.op s) =
      SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm s := by
  apply SSet.yonedaEquiv.injective
  have h := uliftYonedaEquiv_naturality (SSet.yonedaEquiv.symm s) f.op
  have he : uliftYonedaEquiv (SSet.yonedaEquiv.symm s) = s :=
    (SSet.yonedaEquiv (X := A) (n := n)).apply_symm_apply s
  rw [he] at h
  exact ((SSet.yonedaEquiv (X := A) (n := m)).apply_symm_apply _).trans h

/-- Actual singular simplices are maps from the same original realized standard simplex. -/
def singularSimplexHomEquiv (T : TopCat.{u}) (n : SimplexCategory) :
    (TopCat.toSSet.obj T).obj (op n) ≃ (SSet.toTop.obj (SSet.stdSimplex.obj n) ⟶ T) :=
  (SSet.yonedaEquiv (X := TopCat.toSSet.obj T) (n := n)).symm.trans
    (sSetTopAdj.homEquiv (SSet.stdSimplex.obj n) T).symm

/-- This native hom equivalence commutes with every original simplex parameter map. -/
theorem singularSimplexHomEquiv_parameter_naturality (T : TopCat.{u})
    {m n : SimplexCategory} (f : m ⟶ n) (s : (TopCat.toSSet.obj T).obj (op n)) :
    singularSimplexHomEquiv T m ((TopCat.toSSet.obj T).map f.op s) =
      SSet.toTop.map (SSet.stdSimplex.map f) ≫ singularSimplexHomEquiv T n s := by
  change (sSetTopAdj.homEquiv _ _).symm (SSet.yonedaEquiv.symm _) = _
  rw [singularYoneda_symm_parameter_naturality, sSetTopAdj.homEquiv_naturality_left_symm]
  rfl

variable (X : ContAction TopCat.{u} C2.{u}) (a b : FixedPoints X)

/-- The original exponential comparison in every singular degree, with the same endpoints. -/
def equivariantPathSingularDegreeEquiv (n : SimplexCategory) :
    (mappingSing (continuousPathAction X a b)).obj (op n) ≃
    (TopCat.toSSet.obj (continuousPathTop (mappingTop X)
      (constantMap realizedEC2ContinuousAction X a)
      (constantMap realizedEC2ContinuousAction X b))).obj (op n) :=
  (singularSimplexHomEquiv (mappingTop (continuousPathAction X a b)) n).trans
    ((equivariantPathFamilyHomEquiv X a b (SSet.toTop.obj (SSet.stdSimplex.obj n))).trans
      (singularSimplexHomEquiv (continuousPathTop (mappingTop X)
        (constantMap realizedEC2ContinuousAction X a)
        (constantMap realizedEC2ContinuousAction X b)) n).symm)

/-- All original face and degeneracy maps commute with the degreewise comparison. -/
theorem equivariantPathSingularDegreeEquiv_naturality {m n : SimplexCategory}
    (f : m ⟶ n) (s : (mappingSing (continuousPathAction X a b)).obj (op n)) :
    equivariantPathSingularDegreeEquiv X a b m
      ((mappingSing (continuousPathAction X a b)).map f.op s) =
    (TopCat.toSSet.obj (continuousPathTop (mappingTop X)
      (constantMap realizedEC2ContinuousAction X a)
      (constantMap realizedEC2ContinuousAction X b))).map f.op
        (equivariantPathSingularDegreeEquiv X a b n s) := by
  apply (singularSimplexHomEquiv (continuousPathTop (mappingTop X)
    (constantMap realizedEC2ContinuousAction X a)
    (constantMap realizedEC2ContinuousAction X b)) m).injective
  change (singularSimplexHomEquiv _ m) ((singularSimplexHomEquiv _ m).symm
      ((equivariantPathFamilyHomEquiv X a b _)
        ((singularSimplexHomEquiv _ m)
          ((TopCat.toSSet.obj (mappingTop (continuousPathAction X a b))).map f.op s)))) = _
  rw [Equiv.apply_symm_apply, singularSimplexHomEquiv_parameter_naturality,
    equivariantPathFamilyHomEquiv_parameter_naturality,
    singularSimplexHomEquiv_parameter_naturality]
  exact congrArg (fun q ↦ SSet.toTop.map (SSet.stdSimplex.map f) ≫ q)
    ((singularSimplexHomEquiv _ n).apply_symm_apply _).symm

/-- The exact original Sing equivariant-path and Sing mapping-space-path simplicial isomorphism.
-/
def equivariantPathSingularIso :
    mappingSing (continuousPathAction X a b) ≅
      TopCat.toSSet.obj (continuousPathTop (mappingTop X)
        (constantMap realizedEC2ContinuousAction X a)
        (constantMap realizedEC2ContinuousAction X b)) :=
  NatIso.ofComponents (fun n ↦ (equivariantPathSingularDegreeEquiv X a b n.unop).toIso) (by
    intro n m f
    ext s
    exact equivariantPathSingularDegreeEquiv_naturality X a b f.unop s)

/-- This actual original simplicial isomorphism is a native weak equivalence. -/
theorem equivariantPathSingularIso_hom_weakEquivalence :
    WeakEquivalence (equivariantPathSingularIso X a b).hom := by
  infer_instance

/-- Singular of the actual original EC₂-equivariant core paths at the same original vertices. -/
def originalUnitaryEquivariantPathSing (K : DaggerSSet.{u})
    (x y : K.toSSet.obj (op ⦋0⦌)) : SSet.{u} :=
  mappingSing (continuousPathAction
    (realizedContinuousActionFunctor.obj (daggerCoreCandidate K))
    (realizedFixedPoint (daggerCoreCandidate K) ((coreVertexEquiv K).symm x))
    (realizedFixedPoint (daggerCoreCandidate K) ((coreVertexEquiv K).symm y)))

/-- The original core equivariant path object is the same singular continuous unitary path space.
-/
def originalUnitaryEquivariantPathIso (K : DaggerSSet.{u})
    (x y : K.toSSet.obj (op ⦋0⦌)) :
    originalUnitaryEquivariantPathSing K x y ≅ continuousUnitaryPathSing K x y :=
  equivariantPathSingularIso _ _ _

end

end DaggerOriginalEquivariantPathSingularExponential
