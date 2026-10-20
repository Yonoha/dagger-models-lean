import OriginalEquivariantRealizationSingularHomEquiv
import OriginalRealizationLocallyCompactProducts
import OriginalEquivariantPathExponentialTargetNaturality

/-!
# The original enriched EC₂ realization-singular comparison

In each degree the literal equivariant maps from Ebullet C₂ times the original standard simplex
are identified by the native realization-singular adjunction, the original product isomorphism
and original compact-parameter currying. All simplex maps and equivariant target maps commute.
The resulting simplicial isomorphism compares exactly the original enriched mapping object
with singular of the same original equivariant compact-open mapping space.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2RealizationAction DaggerOriginalEquivariantParameterTensor
open DaggerOriginalEC2CompactParameterHomEquiv DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalRealizationLocallyCompactProducts
open DaggerOriginalSimplicialEquivariantParameterTensor
open DaggerOriginalEquivariantRealizationSingularHomEquiv
open DaggerOriginalEquivariantPathSingularExponential
open DaggerOriginalEquivariantPathExponentialTargetNaturality
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalEC2EnrichedRealizationSingularComparison

noncomputable section

/-- The original realized simplex product isomorphism retains the exact original EC₂ action. -/
def realizedEC2ParameterIso (n : SimplexCategory) :
    (SSet.toTop.mapAction C2.{u}).obj
      (simplicialParameterTensor simplicialAction.{u} (SSet.stdSimplex.obj n)) ≅
    originalEC2Tensor (SSet.toTop.obj (SSet.stdSimplex.obj n)) :=
  Action.mkIso (realizationProductIso simplicialEC2 (SSet.stdSimplex.obj n)) (by
    intro g
    change SSet.toTop.map ((simplicialAction.ρ g).asHom ▷ SSet.stdSimplex.obj n) ≫
        (realizationProductIso simplicialEC2 (SSet.stdSimplex.obj n)).hom =
      (realizationProductIso simplicialEC2 (SSet.stdSimplex.obj n)).hom ≫
        (SSet.toTop.map (simplicialAction.ρ g).asHom ▷
          SSet.toTop.obj (SSet.stdSimplex.obj n))
    simpa using realizationProductIso_naturality (simplicialAction.ρ g).asHom
      (𝟙 (SSet.stdSimplex.obj n)))

/-- The same original product isomorphism retains every original simplex parameter map. -/
theorem realizedEC2ParameterIso_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    (SSet.toTop.mapAction C2.{u}).map
      (simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.map f)) ≫
        (realizedEC2ParameterIso n).hom =
    (realizedEC2ParameterIso m).hom ≫
      originalEC2TensorMap (SSet.toTop.map (SSet.stdSimplex.map f)) := by
  apply Action.Hom.ext
  change SSet.toTop.map (simplicialEC2 ◁ SSet.stdSimplex.map f) ≫
      (realizationProductIso simplicialEC2 (SSet.stdSimplex.obj n)).hom =
    (realizationProductIso simplicialEC2 (SSet.stdSimplex.obj m)).hom ≫
      (SSet.toTop.obj simplicialEC2 ◁ SSet.toTop.map (SSet.stdSimplex.map f))
  simpa using realizationProductIso_naturality (𝟙 simplicialEC2) (SSet.stdSimplex.map f)

/-- The inverse isomorphism has the same actual parameter naturality. -/
theorem realizedEC2ParameterIso_inv_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    originalEC2TensorMap (SSet.toTop.map (SSet.stdSimplex.map f)) ≫
      (realizedEC2ParameterIso n).inv =
    (realizedEC2ParameterIso m).inv ≫
      (SSet.toTop.mapAction C2.{u}).map
        (simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.map f)) := by
  apply (cancel_epi (realizedEC2ParameterIso m).hom).1
  rw [← Category.assoc, ← realizedEC2ParameterIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Each original enriched mapping degree is a hom from the same realized standard simplex. -/
def enrichedDegreeTopHomEquiv (X : ContAction TopCat.{u} C2.{u}) (n : SimplexCategory) :
    (originalEC2EnrichedSingMapping X).obj (op n) ≃
      (SSet.toTop.obj (SSet.stdSimplex.obj n) ⟶ mappingTop X) :=
  (equivariantRealizationSingularHomEquiv
    (simplicialParameterTensor simplicialAction (SSet.stdSimplex.obj n)) X).trans
      ((Iso.homFromEquiv (realizedEC2ParameterIso n)).trans
        (originalEC2HomEquiv (SSet.toTop.obj (SSet.stdSimplex.obj n)) X))

/-- The original degree-to-topological-hom equivalence commutes with every original simplex map.
-/
theorem enrichedDegreeTopHomEquiv_parameter_naturality (X : ContAction TopCat.{u} C2.{u})
    {m n : SimplexCategory} (f : m ⟶ n) (q : (originalEC2EnrichedSingMapping X).obj (op n)) :
    enrichedDegreeTopHomEquiv X m ((originalEC2EnrichedSingMapping X).map f.op q) =
      SSet.toTop.map (SSet.stdSimplex.map f) ≫ enrichedDegreeTopHomEquiv X n q := by
  change originalEC2HomEquiv _ X ((realizedEC2ParameterIso m).inv ≫
      equivariantRealizationSingularHomEquiv _ X
        (simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.map f) ≫ q)) =
    SSet.toTop.map (SSet.stdSimplex.map f) ≫
      originalEC2HomEquiv _ X ((realizedEC2ParameterIso n).inv ≫
        equivariantRealizationSingularHomEquiv _ X q)
  rw [equivariantRealizationSingularHomEquiv_parameter_naturality, ← Category.assoc,
    ← realizedEC2ParameterIso_inv_naturality, Category.assoc]
  exact originalEC2HomEquiv_parameter_naturality X _ _

/-- The original degree-to-topological-hom equivalence retains actual target postcomposition. -/
theorem enrichedDegreeTopHomEquiv_target_naturality {X Y : ContAction TopCat.{u} C2.{u}}
    (f : X ⟶ Y) (n : SimplexCategory) (q : (originalEC2EnrichedSingMapping X).obj (op n)) :
    enrichedDegreeTopHomEquiv Y n (q ≫ singularActionMap f) =
      enrichedDegreeTopHomEquiv X n q ≫ postcompose f := by
  change originalEC2HomEquiv _ Y ((realizedEC2ParameterIso n).inv ≫
      equivariantRealizationSingularHomEquiv _ Y (q ≫ singularActionMap f)) =
    originalEC2HomEquiv _ X ((realizedEC2ParameterIso n).inv ≫
      equivariantRealizationSingularHomEquiv _ X q) ≫ postcompose f
  rw [equivariantRealizationSingularHomEquiv_target_naturality, ← Category.assoc]
  exact originalEC2HomEquiv_target_naturality _ f _

/-- The actual enriched mapping degree is the same degree of the original mapping-space Sing. -/
def enrichedSingDegreeEquiv (X : ContAction TopCat.{u} C2.{u}) (n : SimplexCategory) :
    (originalEC2EnrichedSingMapping X).obj (op n) ≃ (mappingSing X).obj (op n) :=
  (enrichedDegreeTopHomEquiv X n).trans (singularSimplexHomEquiv (mappingTop X) n).symm

/-- All original face and degeneracy maps commute with the actual degree equivalence. -/
theorem enrichedSingDegreeEquiv_parameter_naturality (X : ContAction TopCat.{u} C2.{u})
    {m n : SimplexCategory} (f : m ⟶ n) (q : (originalEC2EnrichedSingMapping X).obj (op n)) :
    enrichedSingDegreeEquiv X m ((originalEC2EnrichedSingMapping X).map f.op q) =
      (mappingSing X).map f.op (enrichedSingDegreeEquiv X n q) := by
  apply (singularSimplexHomEquiv (mappingTop X) m).injective
  change (singularSimplexHomEquiv _ m) ((singularSimplexHomEquiv _ m).symm
      (enrichedDegreeTopHomEquiv X m ((originalEC2EnrichedSingMapping X).map f.op q))) =
    singularSimplexHomEquiv _ m ((TopCat.toSSet.obj (mappingTop X)).map f.op
      ((singularSimplexHomEquiv _ n).symm (enrichedDegreeTopHomEquiv X n q)))
  rw [Equiv.apply_symm_apply, enrichedDegreeTopHomEquiv_parameter_naturality,
    singularSimplexHomEquiv_parameter_naturality, Equiv.apply_symm_apply]

/-- The original enriched realization-singular comparison is an actual simplicial isomorphism.
-/
def originalEC2EnrichedSingIso (X : ContAction TopCat.{u} C2.{u}) :
    originalEC2EnrichedSingMapping X ≅ mappingSing X :=
  NatIso.ofComponents (fun n ↦ (enrichedSingDegreeEquiv X n.unop).toIso) (by
    intro n m f
    ext q
    exact enrichedSingDegreeEquiv_parameter_naturality X f.unop q)

/-- The same original simplicial isomorphism is a native weak equivalence. -/
theorem originalEC2EnrichedSingIso_hom_weakEquivalence (X : ContAction TopCat.{u} C2.{u}) :
    WeakEquivalence (originalEC2EnrichedSingIso X).hom := by
  infer_instance

/-- Original equivariant target maps commute with the degree equivalence. -/
theorem enrichedSingDegreeEquiv_target_naturality {X Y : ContAction TopCat.{u} C2.{u}}
    (f : X ⟶ Y) (n : SimplexCategory) (q : (originalEC2EnrichedSingMapping X).obj (op n)) :
    enrichedSingDegreeEquiv Y n (q ≫ singularActionMap f) =
      (TopCat.toSSet.map (postcompose f)).app (op n) (enrichedSingDegreeEquiv X n q) := by
  apply (singularSimplexHomEquiv (mappingTop Y) n).injective
  change (singularSimplexHomEquiv _ n) ((singularSimplexHomEquiv _ n).symm
      (enrichedDegreeTopHomEquiv Y n (q ≫ singularActionMap f))) =
    singularSimplexHomEquiv _ n ((TopCat.toSSet.map (postcompose f)).app (op n)
      ((singularSimplexHomEquiv _ n).symm (enrichedDegreeTopHomEquiv X n q)))
  rw [Equiv.apply_symm_apply, enrichedDegreeTopHomEquiv_target_naturality,
    singularSimplexHomEquiv_target_naturality, Equiv.apply_symm_apply]

/-- The full original enriched realization-singular comparison is natural in original targets.
-/
theorem originalEC2EnrichedSingIso_naturality {X Y : ContAction TopCat.{u} C2.{u}}
    (f : X ⟶ Y) :
    originalEC2EnrichedSingMappingMap f ≫ (originalEC2EnrichedSingIso Y).hom =
      (originalEC2EnrichedSingIso X).hom ≫ TopCat.toSSet.map (postcompose f) := by
  ext n q
  exact enrichedSingDegreeEquiv_target_naturality f n.unop q

end

end DaggerOriginalEC2EnrichedRealizationSingularComparison
