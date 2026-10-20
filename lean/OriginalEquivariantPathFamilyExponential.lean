import OriginalEquivariantFixedEndpointPathAction

/-!
# Original compact-parameter families of equivariant endpoint paths

For every original compact-generated locally compact parameter K, families of equivariant
paths from original EC₂ correspond to paths in the original equivariant mapping space. The
original compact-open spaces, original product maps, pointwise action and fixed endpoints are
retained. No local compactness hypothesis on the original EC₂ is introduced.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Topology DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEquivariantConstantMaps DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalCompactGeneration DaggerOriginalCompactOpenExponentialLaw
open DaggerOriginalEquivariantCompactParameterCurry DaggerOriginalEC2CompactParameterHomEquiv
open DaggerOriginalContinuousEndpointCylinderFamilies
open DaggerOriginalEquivariantFixedEndpointPathAction

universe u

namespace DaggerOriginalEquivariantPathFamilyExponential

noncomputable section

local instance liftedInterval_compact : CompactSpace TopCat.I.{u} :=
  inferInstanceAs (CompactSpace (ULift.{u} unitInterval))

local instance liftedInterval_t2 : T2Space TopCat.I.{u} :=
  inferInstanceAs (T2Space (ULift.{u} unitInterval))

local instance parameterProduct_generated (K : TopCat.{u})
    [IsGeneratedBy compactHausFamily.{u} K] :
    IsGeneratedBy compactHausFamily.{u} (K × TopCat.I.{u}) :=
  generated_product (E := K) (K := TopCat.I.{u})

variable (X : ContAction TopCat.{u} C2.{u}) (a b : FixedPoints X)
variable (K : TopCat.{u}) [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]

/-- The original equivariant path family gives a cylinder in the original mapping space. -/
def equivariantPathFamilyCylinder (F : K ⟶ mappingTop (continuousPathAction X a b)) :
    constantEndpointCylinders K (mappingTop X)
      (constantMap realizedEC2ContinuousAction X a) (constantMap realizedEC2ContinuousAction X b) :=
  let q := (equivariantCurryEquiv realizedEC2ContinuousAction
    (continuousPathAction X a b) K).symm F.hom
  let h := (constantCylinderPathFamilyEquiv
    (TopCat.of (realizedEC2ContinuousAction.{u}.obj.V × K)) X.obj.V a.val b.val).symm
      (TopCat.ofHom q.val)
  let r : EquivariantProductMaps realizedEC2ContinuousAction X (K × TopCat.I.{u}) :=
    ⟨h.val.hom.comp
      ⟨fun p ↦ ((p.1, p.2.1), p.2.2),
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd)⟩, by
      intro g e kt
      change ((F kt.1).val ((realizedEC2ContinuousAction.obj.ρ g).asHom e)).toContinuousMap
          kt.2.down =
        (X.obj.ρ g).asHom (((F kt.1).val e).toContinuousMap kt.2.down)
      exact congrArg (fun p : _root_.Path a.val b.val ↦ p.toContinuousMap kt.2.down)
        ((F kt.1).property g e)⟩
  ⟨TopCat.ofHom (equivariantCurryEquiv realizedEC2ContinuousAction X (K × TopCat.I.{u}) r), by
    constructor
    · apply ConcreteCategory.hom_ext
      intro k
      apply Subtype.ext
      ext e
      change ((F k).val e).toContinuousMap 0 = a.val
      exact ((F k).val e).source
    · apply ConcreteCategory.hom_ext
      intro k
      apply Subtype.ext
      ext e
      change ((F k).val e).toContinuousMap 1 = b.val
      exact ((F k).val e).target⟩

/-- The same original family gives paths between the original constant equivariant maps. -/
def equivariantPathFamilyForward (F : K ⟶ mappingTop (continuousPathAction X a b)) :
    K ⟶ continuousPathTop (mappingTop X)
      (constantMap realizedEC2ContinuousAction X a) (constantMap realizedEC2ContinuousAction X b) :=
  constantCylinderPathFamilyEquiv K (mappingTop X) _ _
    (equivariantPathFamilyCylinder X a b K F)

/-- A family of original mapping-space paths gives the original equivariant path family. -/
def equivariantPathFamilyBackward
    (G : K ⟶ continuousPathTop (mappingTop X)
      (constantMap realizedEC2ContinuousAction X a) (constantMap realizedEC2ContinuousAction X b)) :
    K ⟶ mappingTop (continuousPathAction X a b) :=
  let c := (constantCylinderPathFamilyEquiv K (mappingTop X)
    (constantMap realizedEC2ContinuousAction X a)
    (constantMap realizedEC2ContinuousAction X b)).symm G
  let r := (equivariantCurryEquiv realizedEC2ContinuousAction X (K × TopCat.I.{u})).symm
    c.val.hom
  let h : constantEndpointCylinders
      (TopCat.of (realizedEC2ContinuousAction.{u}.obj.V × K)) X.obj.V a.val b.val :=
    ⟨TopCat.ofHom (r.val.comp
      ⟨fun p ↦ (p.1.1, (p.1.2, p.2)),
        (continuous_fst.comp continuous_fst).prodMk
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)⟩), by
      constructor
      · apply ConcreteCategory.hom_ext
        intro ek
        exact congrArg (fun q : mappingTop X ↦ q.val ek.1)
          (ConcreteCategory.congr_hom c.property.1 ek.2)
      · apply ConcreteCategory.hom_ext
        intro ek
        exact congrArg (fun q : mappingTop X ↦ q.val ek.1)
          (ConcreteCategory.congr_hom c.property.2 ek.2)⟩
  let q : EquivariantProductMaps realizedEC2ContinuousAction (continuousPathAction X a b) K :=
    ⟨(constantCylinderPathFamilyEquiv _ X.obj.V a.val b.val h).hom, by
      intro g e k
      apply Path.ext
      funext t
      change r.val ((realizedEC2ContinuousAction.obj.ρ g).asHom e, (k, ULift.up t)) =
        (X.obj.ρ g).asHom (r.val (e, (k, ULift.up t)))
      exact r.property g e (k, ULift.up t)⟩
  TopCat.ofHom (equivariantCurryEquiv realizedEC2ContinuousAction (continuousPathAction X a b) K q)

/-- Forward evaluation is precisely evaluation at the same original point and time. -/
theorem equivariantPathFamilyForward_apply (F : K ⟶ mappingTop (continuousPathAction X a b))
    (k : K) (e : realizedEC2ContinuousAction.{u}.obj.V) (t : unitInterval) :
    ((equivariantPathFamilyForward X a b K F k).toContinuousMap t).val e =
      ((F k).val e).toContinuousMap t := rfl

/-- Backward evaluation retains the same original point and time. -/
theorem equivariantPathFamilyBackward_apply
    (G : K ⟶ continuousPathTop (mappingTop X)
      (constantMap realizedEC2ContinuousAction X a) (constantMap realizedEC2ContinuousAction X b))
    (k : K) (e : realizedEC2ContinuousAction.{u}.obj.V) (t : unitInterval) :
    ((equivariantPathFamilyBackward X a b K G k).val e).toContinuousMap t =
      ((G k).toContinuousMap t).val e := rfl

/-- The exact original compact-parameter family equivalence. -/
def equivariantPathFamilyHomEquiv :
    (K ⟶ mappingTop (continuousPathAction X a b)) ≃
    (K ⟶ continuousPathTop (mappingTop X)
      (constantMap realizedEC2ContinuousAction X a) (constantMap realizedEC2ContinuousAction X b))
    where
  toFun := equivariantPathFamilyForward X a b K
  invFun := equivariantPathFamilyBackward X a b K
  left_inv F := by
    apply ConcreteCategory.hom_ext
    intro k
    apply Subtype.ext
    ext e
    apply Path.ext
    funext t
    rfl
  right_inv G := by
    apply ConcreteCategory.hom_ext
    intro k
    apply Path.ext
    funext t
    apply Subtype.ext
    ext e
    rfl

/-- The equivalence commutes with every actual original compact-parameter map. -/
theorem equivariantPathFamilyHomEquiv_parameter_naturality {L : TopCat.{u}}
    [IsGeneratedBy compactHausFamily.{u} L] [LocallyCompactSpace L]
    (i : K ⟶ L) (F : L ⟶ mappingTop (continuousPathAction X a b)) :
    equivariantPathFamilyHomEquiv X a b K (i ≫ F) =
      i ≫ equivariantPathFamilyHomEquiv X a b L F := by
  apply ConcreteCategory.hom_ext
  intro k
  apply Path.ext
  funext t
  apply Subtype.ext
  ext e
  rfl

end

end DaggerOriginalEquivariantPathFamilyExponential
