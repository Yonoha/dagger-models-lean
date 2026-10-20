import OriginalOrdinaryEndpointTransportReconciled
import OrdinaryAnodyneTensor
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Hom retracts in the original simplicial category

An arrow retract in the actual original simplicial category induces an arrow
retract on every source Hom simplicial set. Endpoint transports are retained in
all four square legs. Consequently every retract-stable simplicial-set
morphism property gives a retract-stable local Hom property.
-/

set_option autoImplicit false

open CategoryTheory MorphismProperty HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OriginalOrdinaryHomRetracts

open OriginalOrdinaryEndpointTransport

noncomputable section

variable {C D C' D' : SimplicialCat.{u, u}} {f : C ⟶ D} {g : C' ⟶ D'}
  (h : RetractArrow f g)

/-- The source object retract at an actual original object. -/
def sourceSplit (a : C.Obj) : h.r.left.obj (h.i.left.obj a) = a :=
  congrArg (fun T : C ⟶ C ↦ T.obj a) h.retract_left

/-- The target object retract at an actual original object. -/
def targetSplit (d : D.Obj) : h.r.right.obj (h.i.right.obj d) = d :=
  congrArg (fun T : D ⟶ D ↦ T.obj d) h.retract_right

/-- The inclusion square's equality of target endpoints. -/
def inclusionEndpoint (a : C.Obj) :
    g.obj (h.i.left.obj a) = h.i.right.obj (f.obj a) :=
  congrArg (fun T : C ⟶ D' ↦ T.obj a) h.i_w

/-- The retraction square's equality of target endpoints. -/
def retractionEndpoint (a : C.Obj) :
    h.r.right.obj (g.obj (h.i.left.obj a)) = f.obj a :=
  (congrArg (fun T : C' ⟶ D ↦ T.obj (h.i.left.obj a)) h.r_w).symm.trans
    (congrArg f.obj (sourceSplit h a))

/-- Source leg of the Hom-arrow inclusion. -/
abbrev inclusionSource (a b : C.Obj) := h.i.left.map a b

/-- Target leg of the Hom-arrow inclusion, cast to the actual `g` endpoints. -/
def inclusionTarget (a b : C.Obj) :
    D.enriched.Hom (f.obj a) (f.obj b) ⟶
      D'.enriched.Hom (g.obj (h.i.left.obj a)) (g.obj (h.i.left.obj b)) :=
  h.i.right.map (f.obj a) (f.obj b) ≫
    transport D' (inclusionEndpoint h a).symm (inclusionEndpoint h b).symm

/-- Source leg of the Hom-arrow retraction, cast to the original pair. -/
def retractionSource (a b : C.Obj) :
    C'.enriched.Hom (h.i.left.obj a) (h.i.left.obj b) ⟶
      C.enriched.Hom a b :=
  h.r.left.map (h.i.left.obj a) (h.i.left.obj b) ≫
    transport C (sourceSplit h a) (sourceSplit h b)

/-- Target leg of the Hom-arrow retraction, cast to the original pair. -/
def retractionTarget (a b : C.Obj) :
    D'.enriched.Hom (g.obj (h.i.left.obj a)) (g.obj (h.i.left.obj b)) ⟶
      D.enriched.Hom (f.obj a) (f.obj b) :=
  h.r.right.map (g.obj (h.i.left.obj a)) (g.obj (h.i.left.obj b)) ≫
    transport D (retractionEndpoint h a) (retractionEndpoint h b)

/-- The inclusion respects the original Hom map with its endpoint cast. -/
theorem inclusion_square (a b : C.Obj) :
    inclusionSource h a b ≫ g.map (h.i.left.obj a) (h.i.left.obj b) =
      f.map a b ≫ inclusionTarget h a b := by
  have e := congrArg (fun t ↦ t ≫
    transport D' (inclusionEndpoint h a).symm (inclusionEndpoint h b).symm)
    (map_of_eq h.i_w a b)
  simpa only [SimplicialCat.comp_map, SimplicialCat.comp_obj,
    Category.assoc, transport_comp, transport_refl, Category.comp_id,
    inclusionSource, inclusionTarget] using e

/-- The retraction respects the original Hom map with its endpoint cast. -/
theorem retraction_square (a b : C.Obj) :
    retractionSource h a b ≫ f.map a b =
      g.map (h.i.left.obj a) (h.i.left.obj b) ≫ retractionTarget h a b := by
  have e := congrArg (fun t ↦ t ≫
    transport D (retractionEndpoint h a) (retractionEndpoint h b))
    (map_of_eq h.r_w (h.i.left.obj a) (h.i.left.obj b))
  rw [retractionSource, Category.assoc, transport_map]
  simpa only [SimplicialCat.comp_map, SimplicialCat.comp_obj,
    Category.assoc, transport_comp, retractionTarget] using e

/-- The source Hom leg of the arrow diagram splits. -/
theorem source_retract (a b : C.Obj) :
    inclusionSource h a b ≫ retractionSource h a b = 𝟙 _ := by
  simpa only [SimplicialCat.comp_map, SimplicialCat.comp_obj,
    SimplicialCat.id_map, Category.assoc, inclusionSource, retractionSource]
    using map_of_eq h.retract_left a b

/-- The target Hom leg of the arrow diagram splits. -/
theorem target_retract (a b : C.Obj) :
    inclusionTarget h a b ≫ retractionTarget h a b = 𝟙 _ := by
  have t :
      transport D (congrArg h.r.right.obj (inclusionEndpoint h a).symm)
        (congrArg h.r.right.obj (inclusionEndpoint h b).symm) ≫
        transport D (retractionEndpoint h a) (retractionEndpoint h b) =
          transport D (targetSplit h (f.obj a)) (targetSplit h (f.obj b)) :=
    transport_comp D _ _ _ _
  calc
    _ = h.i.right.map (f.obj a) (f.obj b) ≫
        h.r.right.map (h.i.right.obj (f.obj a)) (h.i.right.obj (f.obj b)) ≫
        transport D (targetSplit h (f.obj a)) (targetSplit h (f.obj b)) := by
      rw [inclusionTarget, retractionTarget, Category.assoc, ← Category.assoc
        (transport D' _ _) (h.r.right.map _ _) _, transport_map]
      simpa only [Category.assoc] using congrArg
        (fun v ↦ h.i.right.map (f.obj a) (f.obj b) ≫
          h.r.right.map (h.i.right.obj (f.obj a)) (h.i.right.obj (f.obj b)) ≫ v) t
    _ = 𝟙 _ := by
      simpa only [SimplicialCat.comp_map, SimplicialCat.comp_obj,
        SimplicialCat.id_map, Category.assoc]
        using map_of_eq h.retract_right (f.obj a) (f.obj b)

/-- Every actual original Hom arrow is a retract at the transported pair. -/
def homRetract (a b : C.Obj) :
    RetractArrow (f.map a b) (g.map (h.i.left.obj a) (h.i.left.obj b)) where
  i := Arrow.homMk (inclusionSource h a b) (inclusionTarget h a b)
    (inclusion_square h a b)
  r := Arrow.homMk (retractionSource h a b) (retractionTarget h a b)
    (retraction_square h a b)
  retract := Arrow.hom_ext _ _ (source_retract h a b) (target_retract h a b)

/-- The property that all actual original Hom maps lie in `P`. -/
def localHomProperty (P : MorphismProperty SSet.{u}) :
    MorphismProperty SimplicialCat.{u, u} :=
  fun C _ f ↦ ∀ a b : C.Obj, P (f.map a b)

theorem localHomProperty_iff (P : MorphismProperty SSet.{u})
    {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    localHomProperty P F ↔ ∀ a b : C.Obj, P (F.map a b) := Iff.rfl

/-- A retract-stable simplicial-set property is locally retract-stable. -/
instance localHomProperty_isStableUnderRetracts (P : MorphismProperty SSet.{u})
    [P.IsStableUnderRetracts] : (localHomProperty P).IsStableUnderRetracts where
  of_retract h hg := by
    intro a b
    exact P.of_retract (homRetract h a b) (hg (h.i.left.obj a) (h.i.left.obj b))

/-- Local Hom properties inherit identities and composition. -/
instance localHomProperty_isMultiplicative (P : MorphismProperty SSet.{u})
    [P.IsMultiplicative] : (localHomProperty P).IsMultiplicative where
  id_mem C := by
    intro a b
    simpa only [SimplicialCat.id_map] using P.id_mem (a ⟶[SSet.{u}] b)
  comp_mem F G hF hG := by
    intro a b
    rw [SimplicialCat.comp_map]
    exact P.comp_mem _ _ (hF a b) (hG (F.obj a) (F.obj b))

/-- The actual ordinary local anodyne class is retract-stable. -/
instance localAnodyne_isStableUnderRetracts :
    (localHomProperty SSet.anodyneExtensions.{u}).IsStableUnderRetracts where
  of_retract h hg := by
    intro a b
    apply (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).2
    apply MorphismProperty.of_retract (P := trivialCofibrations SSet.{u})
      (homRetract h a b)
    exact (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
      (hg (h.i.left.obj a) (h.i.left.obj b))

/-- The actual Quillen local trivial-cofibration class is retract-stable. -/
instance localTrivialCofibration_isStableUnderRetracts :
    (localHomProperty (trivialCofibrations SSet.{u})).IsStableUnderRetracts :=
  localHomProperty_isStableUnderRetracts _

end

end DaggerModels.OriginalOrdinaryHomRetracts
