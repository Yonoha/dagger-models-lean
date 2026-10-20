import OriginalGateNecklaceColimit

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {d : ℕ}

/-- The actual flank inclusion is monomorphic, independently of the target. -/
theorem flankInclusion_mono {T : NecklaceCode} (F : Flag.{u} T d) :
    Mono (flankInclusion F).map := by
  apply necklace_map_mono_of_vertex_injective
  intro x y h
  apply (flankCode F).verticesEquiv.injective
  apply flankVertex_injective F
  rw [← flankInclusion_vertex, ← flankInclusion_vertex]
  change T.verticesEquiv ((flankInclusion F).map.app _
    ((flankCode F).verticesEquiv.symm ((flankCode F).verticesEquiv x))) = _
  simpa only [mapVertices, Equiv.symm_apply_apply] using congrArg T.verticesEquiv h

/-- Restricting a monomorphic over-X necklace to its flank remains monomorphic. -/
theorem flankOver_mono (P : NecklacesOver X a b) (F : Flag.{u} P.code d)
    (hP : Mono P.map) : Mono (flankOver P F).map := by
  have := flankInclusion_mono F
  change Mono ((flankInclusion F).map ≫ P.map)
  infer_instance

variable (a b) (S : Set (X.obj (op ⦋0⦌)))

/-- Forgetting the restriction sends each actual representative to the same original Hom class. -/
def monicGateToHom : monicGateHom a b S ⟶ flagHom X a b where
  app q := Quot.lift (fun p ↦ Quot.mk _ (⟨p.1.obj, p.2⟩ : RawFlag X a b q)) (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨f, hf⟩
    exact Quot.sound ⟨f.hom, hf⟩)
  naturality p q α := by
    funext x
    induction x using Quot.ind with | _ x
    rfl

/-- The comparison lands in the literal gate subcomplex, by the actual joint condition. -/
def monicGateComparison :
    monicGateHom a b S ⟶ (flagGateSubcomplex a b S).toFunctor where
  app q x := ⟨(monicGateToHom a b S).app q x, by
    induction x using Quot.ind with
    | _ p => exact p.1.property.2.trans (necklaceJointImage_subset_support p.1.obj p.2)⟩
  naturality p q α := by
    funext x
    apply Subtype.ext
    exact congrFun ((monicGateToHom a b S).naturality α) x

/-- The comparison is the original inclusion on every specified necklace leg. -/
theorem monicGateComparison_leg (P : MonicGateNecklaces a b S) :
    monicGateLeg a b S P ≫ monicGateComparison a b S ≫ (flagGateSubcomplex a b S).ι =
      flagLeg X a b P.obj := rfl

variable {a b S}

/-- The flank of a gate representative lies in the same restricted full subcategory. -/
def monicGateFlank (p : MonicGateRawFlag a b S (op ⦋d⦌)) : MonicGateNecklaces a b S :=
  ⟨flankOver p.1.obj p.2, flankOver_mono p.1.obj p.2 p.1.property.1, by
    have hc := flankification_class (⟨p.1.obj, p.2⟩ : Degree X a b d)
    have hs := flagVertexSupport_flanked (flankOver p.1.obj p.2) (flankFlag p.2)
      (flankFlag_flanked p.2)
    rw [← hs]
    change S ⊆ flagVertexSupport (classOf X a b d
      (flankDegreeObj (⟨p.1.obj, p.2⟩ : Degree X a b d)))
    change classOf X a b d (flankDegreeObj ⟨p.1.obj, p.2⟩) = _ at hc
    rw [hc]
    exact p.1.property.2.trans (necklaceJointImage_subset_support p.1.obj p.2)⟩

/-- The original flank arrow already generates equality in the restricted colimit. -/
theorem monicGateFlank_class (p : MonicGateRawFlag a b S (op ⦋d⦌)) :
    Quot.mk (monicGateRelation a b S (op ⦋d⦌)) ⟨monicGateFlank p, flankFlag p.2⟩ =
      Quot.mk _ p := by
  exact Quot.sound ⟨ObjectProperty.homMk (inclusionOver ⟨p.1.obj, p.2⟩),
    (flankInclusion_flag p.2).symm⟩

variable (hm : ∀ P : NecklacesOver X a b,
  (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)

/-- P1's existing center, viewed as a monomorphic gate necklace, for the same original class. -/
def monicGateCenter (x : (flagGateSubcomplex a b S).obj (op ⦋d⦌)) :
    MonicGateNecklaces a b S :=
  ⟨(fiberCenter X a b d x.val).obj.obj.1,
    hm _ (fiberCenter_nondegenerate X a b d x.val), by
    have hs := flagVertexSupport_flanked (fiberCenter X a b d x.val).obj.obj.1
      (fiberCenter X a b d x.val).obj.obj.2 (fiberCenter X a b d x.val).property
    change flagVertexSupport (classOf X a b d (fiberCenter X a b d x.val).obj.obj) = _ at hs
    rw [fiberCenter_class] at hs
    exact hs ▸ x.property⟩

/-- The center's original flag, without changing its necklace, degree, or gate data. -/
def monicGateCenterFlag (x : (flagGateSubcomplex a b S).obj (op ⦋d⦌)) :
    Flag.{u} (monicGateCenter hm x).obj.code d :=
  (fiberCenter X a b d x.val).obj.obj.2

/-- P1's terminal arrow identifies any representative of x with its center inside the restriction. -/
theorem monicGate_class_eq_center (p : MonicGateRawFlag a b S (op ⦋d⦌))
    (x : (flagGateSubcomplex a b S).obj (op ⦋d⦌))
    (hx : Quot.mk (flagRelation X a b (op ⦋d⦌)) ⟨p.1.obj, p.2⟩ = x.val) :
    Quot.mk (monicGateRelation a b S (op ⦋d⦌)) p =
      Quot.mk _ ⟨monicGateCenter hm x, monicGateCenterFlag hm x⟩ := by
  let fp : FlankedFiber X a b d x.val :=
    (flankToFlankedFiber X a b d x.val).obj ⟨⟨p.1.obj, p.2⟩, hx⟩
  let f := (fiberCenterIsTerminal X a b d x.val).from fp
  apply (monicGateFlank_class p).symm.trans
  exact Quot.sound ⟨ObjectProperty.homMk f.hom.hom.val, f.hom.hom.property.symm⟩

include hm in
/-- Equality in the original Hom implies equality in the restricted necklace colimit. -/
theorem monicGateComparison_injective :
    Function.Injective ((monicGateComparison a b S).app (op ⦋d⦌)) := by
  intro p q h
  induction p using Quot.ind with
  | _ p =>
    induction q using Quot.ind with
    | _ q =>
      let x := (monicGateComparison a b S).app (op ⦋d⦌) (Quot.mk _ p)
      exact (monicGate_class_eq_center hm p x rfl).trans
        (monicGate_class_eq_center hm q x (congrArg Subtype.val h).symm).symm

include hm in
/-- Every gate simplex is represented by the same P1 center in the restricted colimit. -/
theorem monicGateComparison_surjective :
    Function.Surjective ((monicGateComparison a b S).app (op ⦋d⦌)) := by
  intro x
  refine ⟨Quot.mk _ ⟨monicGateCenter hm x, monicGateCenterFlag hm x⟩, ?_⟩
  apply Subtype.ext
  exact fiberCenter_class X a b d x.val

end

end DaggerOriginalProductGadget
