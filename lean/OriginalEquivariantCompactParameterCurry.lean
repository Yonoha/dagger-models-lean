import OriginalCompactOpenExponentialLaw
import OriginalEC2HomotopyFixedPointFunctor

/-!
# Original equivariant compact-open families and product maps

The equivalence retains the original continuous action, ordinary product, and
compact-open equivariance subtype. It uses generation of the actual domain and
local compactness only of the parameter. Naturality in the parameter is explicit.
No model-class preservation statement is assumed.
-/

set_option autoImplicit false

open CategoryTheory Topology DaggerModels
open DaggerOriginalCompactGeneration DaggerOriginalCompactOpenExponentialLaw
open DaggerOriginalEquivariantConstantMaps DaggerOriginalDaggerRealizationC2Action

universe u

namespace DaggerOriginalEquivariantCompactParameterCurry

noncomputable section

variable (E X : ContAction TopCat.{u} C2.{u}) (K : Type u) [TopologicalSpace K]

/-- Equivariant maps from the literal product, with trivial action on the parameter. -/
def EquivariantProductMaps :=
  {f : C(E.obj.V × K, X.obj.V) // ∀ (g : C2.{u}) (e : E.obj.V) (k : K),
    f ((E.obj.ρ g).asHom e, k) = (X.obj.ρ g).asHom (f (e, k))}

/-- Families into the original equivariance subtype correspond to actual equivariant product
maps. -/
def equivariantCurryEquiv [IsGeneratedBy compactHausFamily.{u} E.obj.V]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K] :
    EquivariantProductMaps E X K ≃ C(K, EquivariantMaps E X) where
  toFun f :=
    ⟨fun k ↦ ⟨compactParameterCurryEquiv f.val k, fun g e ↦ f.property g e k⟩,
      (compactParameterCurryEquiv f.val).continuous.subtype_mk _⟩
  invFun f :=
    ⟨compactParameterCurryEquiv.symm
      ⟨fun k ↦ (f k).val, continuous_subtype_val.comp f.continuous⟩,
      fun g e k ↦ (f k).property g e⟩
  left_inv f := by
    apply Subtype.ext
    ext ⟨e, k⟩
    rfl
  right_inv f := by
    ext k
    rfl

/-- Currying evaluates the same original product map. -/
theorem equivariantCurryEquiv_apply [IsGeneratedBy compactHausFamily.{u} E.obj.V]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    (f : EquivariantProductMaps E X K) (k : K) (e : E.obj.V) :
    (equivariantCurryEquiv E X K f k).val e = f.val (e, k) := rfl

/-- Uncurrying evaluates the same original equivariant family. -/
theorem equivariantCurryEquiv_symm_apply [IsGeneratedBy compactHausFamily.{u} E.obj.V]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    (f : C(K, EquivariantMaps E X)) (e : E.obj.V) (k : K) :
    ((equivariantCurryEquiv E X K).symm f).val (e, k) = (f k).val e := rfl

variable {E X K}

/-- Precomposition acts on the actual parameter factor of an equivariant product map. -/
def parameterPrecompose {L : Type u} [TopologicalSpace L] (i : C(L, K))
    (f : EquivariantProductMaps E X K) : EquivariantProductMaps E X L :=
  ⟨f.val.comp ⟨fun p ↦ (p.1, i p.2),
      continuous_fst.prodMk (i.continuous.comp continuous_snd)⟩,
    fun g e l ↦ f.property g e (i l)⟩

/-- The equivalence commutes with the literal precomposition of parameter maps. -/
theorem equivariantCurryEquiv_parameter_naturality
    [IsGeneratedBy compactHausFamily.{u} E.obj.V]
    [IsGeneratedBy compactHausFamily.{u} K] [LocallyCompactSpace K]
    {L : Type u} [TopologicalSpace L]
    [IsGeneratedBy compactHausFamily.{u} L] [LocallyCompactSpace L]
    (i : C(L, K)) (f : EquivariantProductMaps E X K) :
    equivariantCurryEquiv E X L (parameterPrecompose i f) =
      (equivariantCurryEquiv E X K f).comp i := by
  ext l
  rfl

end

end DaggerOriginalEquivariantCompactParameterCurry
