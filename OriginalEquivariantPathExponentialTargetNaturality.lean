import OriginalEquivariantPathSingularExponential

/-!
# Original target naturality of the equivariant path exponential comparison

The actual equivariant target map acts pointwise on original paths and by postcomposition on
the original mapping spaces. Explicit original fixed endpoint labels are retained. Both the
compact-parameter hom equivalence and the full singular isomorphism commute with these maps.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Topology DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEquivariantConstantMaps DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalCompactGeneration
open DaggerOriginalContinuousEndpointCylinderFamilies DaggerOriginalLabeledPathFiberNaturality
open DaggerOriginalEquivariantFixedEndpointPathAction DaggerOriginalEquivariantPathFamilyExponential
open DaggerOriginalEquivariantPathSingularExponential

universe u

namespace DaggerOriginalEquivariantPathExponentialTargetNaturality

noncomputable section

variable {X Y : ContAction TopCat.{u} C2.{u}} (f : X ⟶ Y)
variable (a b : FixedPoints X) (a' b' : FixedPoints Y)
variable (ha : f.hom.hom a.val = a'.val) (hb : f.hom.hom b.val = b'.val)

/-- The actual equivariant target map acts pointwise on the same original endpoint paths. -/
def continuousPathActionMap : continuousPathAction X a b ⟶ continuousPathAction Y a' b' :=
  ObjectProperty.homMk
    { hom := labeledContinuousPathTopMap f.hom.hom a.val b.val a'.val b'.val ha hb
      comm g := by
        apply ConcreteCategory.hom_ext
        intro p
        apply Path.ext
        funext t
        exact ConcreteCategory.congr_hom (f.hom.comm g) (p.toContinuousMap t) }

include ha in
/-- The original equivariant constant map is sent to the original labelled target constant. -/
theorem equivariantConstantMap_naturality :
    postcompose f (constantMap realizedEC2ContinuousAction X a) =
      constantMap realizedEC2ContinuousAction Y a' := by
  apply Subtype.ext
  ext e
  exact ha

/-- The actual original mapping-space path map at the same original constant endpoints. -/
def mappingSpacePathMap :
    continuousPathTop (mappingTop X)
      (constantMap realizedEC2ContinuousAction X a) (constantMap realizedEC2ContinuousAction X b) ⟶
    continuousPathTop (mappingTop Y)
      (constantMap realizedEC2ContinuousAction Y a')
      (constantMap realizedEC2ContinuousAction Y b') :=
  labeledContinuousPathTopMap (postcompose f) _ _ _ _
    (equivariantConstantMap_naturality f a a' ha)
    (equivariantConstantMap_naturality f b b' hb)

/-- Original compact-parameter families commute with the same actual equivariant target map. -/
theorem equivariantPathFamilyHomEquiv_target_naturality (K : TopCat.{u})
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    (F : K ⟶ mappingTop (continuousPathAction X a b)) :
    equivariantPathFamilyHomEquiv Y a' b' K
      (F ≫ postcompose (continuousPathActionMap f a b a' b' ha hb)) =
    equivariantPathFamilyHomEquiv X a b K F ≫ mappingSpacePathMap f a b a' b' ha hb := by
  apply ConcreteCategory.hom_ext
  intro k
  apply Path.ext
  funext t
  apply Subtype.ext
  ext e
  rfl

/-- The native realized-simplex hom equivalence commutes with original target postcomposition. -/
theorem singularSimplexHomEquiv_target_naturality {T U : TopCat.{u}} (k : T ⟶ U)
    (n : SimplexCategory) (s : (TopCat.toSSet.obj T).obj (op n)) :
    singularSimplexHomEquiv U n ((TopCat.toSSet.map k).app (op n) s) =
      singularSimplexHomEquiv T n s ≫ k := by
  change (sSetTopAdj.homEquiv _ _).symm (SSet.yonedaEquiv.symm _) = _
  rw [← SSet.yonedaEquiv_symm_comp, sSetTopAdj.homEquiv_naturality_right_symm]
  rfl

/-- The original exponential comparison commutes with target maps in every singular degree. -/
theorem equivariantPathSingularDegreeEquiv_target_naturality (n : SimplexCategory)
    (s : (mappingSing (continuousPathAction X a b)).obj (op n)) :
    equivariantPathSingularDegreeEquiv Y a' b' n
      ((TopCat.toSSet.map (postcompose (continuousPathActionMap f a b a' b' ha hb))).app
        (op n) s) =
    (TopCat.toSSet.map (mappingSpacePathMap f a b a' b' ha hb)).app (op n)
      (equivariantPathSingularDegreeEquiv X a b n s) := by
  apply (singularSimplexHomEquiv (continuousPathTop (mappingTop Y)
    (constantMap realizedEC2ContinuousAction Y a')
    (constantMap realizedEC2ContinuousAction Y b')) n).injective
  change (singularSimplexHomEquiv _ n) ((singularSimplexHomEquiv _ n).symm
      ((equivariantPathFamilyHomEquiv Y a' b' _)
        ((singularSimplexHomEquiv _ n)
          ((TopCat.toSSet.map (postcompose (continuousPathActionMap f a b a' b' ha hb))).app
            (op n) s)))) = _
  rw [Equiv.apply_symm_apply, singularSimplexHomEquiv_target_naturality,
    equivariantPathFamilyHomEquiv_target_naturality,
    singularSimplexHomEquiv_target_naturality]
  exact congrArg (fun q ↦ q ≫ mappingSpacePathMap f a b a' b' ha hb)
    ((singularSimplexHomEquiv _ n).apply_symm_apply _).symm

/-- The full original singular isomorphism is natural in equivariant bipointed target maps. -/
theorem equivariantPathSingularIso_naturality :
    TopCat.toSSet.map (postcompose (continuousPathActionMap f a b a' b' ha hb)) ≫
      (equivariantPathSingularIso Y a' b').hom =
    (equivariantPathSingularIso X a b).hom ≫
      TopCat.toSSet.map (mappingSpacePathMap f a b a' b' ha hb) := by
  ext n s
  exact equivariantPathSingularDegreeEquiv_target_naturality f a b a' b' ha hb n.unop s

end

end DaggerOriginalEquivariantPathExponentialTargetNaturality
