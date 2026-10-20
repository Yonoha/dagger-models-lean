import OriginalEquivariantCompactParameterCurry

/-!
# Literal parameter products of the original continuous actions

The action operates on the original first factor and trivially on the parameter.
Its equivariant morphisms are exactly the previously defined equivariant product
maps. No compactification or replacement of the original action is introduced.
-/

set_option autoImplicit false

open CategoryTheory Topology DaggerModels
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEquivariantCompactParameterCurry

universe u

namespace DaggerOriginalEquivariantParameterTensor

noncomputable section

/-- The original action tensored with a trivially acted-on parameter, using the ordinary product. -/
def parameterTensor (E : ContAction TopCat.{u} C2.{u}) (K : TopCat.{u}) :
    Action TopCat.{u} C2.{u} where
  V := TopCat.of (E.obj.V × K)
  ρ :=
    { toFun g := End.of (TopCat.ofHom
        ⟨fun p ↦ ((E.obj.ρ g).asHom p.1, p.2),
          ((E.obj.ρ g).asHom.hom.continuous.comp continuous_fst).prodMk continuous_snd⟩)
      map_one' := by
        apply End.ext
        apply ConcreteCategory.hom_ext
        intro p
        exact Prod.ext (ConcreteCategory.congr_hom (congrArg End.asHom E.obj.ρ.map_one) p.1) rfl
      map_mul' g h := by
        apply End.ext
        apply ConcreteCategory.hom_ext
        intro p
        exact Prod.ext
          (ConcreteCategory.congr_hom (congrArg End.asHom (E.obj.ρ.map_mul g h)) p.1) rfl }

/-- A parameter map acts on precisely the second factor of the original product. -/
def parameterTensorMap (E : ContAction TopCat.{u} C2.{u}) {K L : TopCat.{u}} (i : K ⟶ L) :
    parameterTensor E K ⟶ parameterTensor E L where
  hom := TopCat.ofHom
    ⟨fun p ↦ (p.1, i p.2), continuous_fst.prodMk (i.hom.continuous.comp continuous_snd)⟩
  comm _ := by
    ext p
    rfl

/-- Morphisms from the original parameter product have exactly the original equivariance formula. -/
def equivariantProductHomEquiv (E X : ContAction TopCat.{u} C2.{u}) (K : TopCat.{u}) :
    (parameterTensor E K ⟶ X.obj) ≃ EquivariantProductMaps E X K where
  toFun f := ⟨f.hom.hom, fun g e k ↦ ConcreteCategory.congr_hom (f.comm g) (e, k)⟩
  invFun f :=
    { hom := TopCat.ofHom f.val
      comm g := by
        ext ⟨e, k⟩
        exact f.property g e k }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Parameter precomposition is exactly composition with the literal product map. -/
theorem equivariantProductHomEquiv_parameter_naturality
    (E X : ContAction TopCat.{u} C2.{u}) {K L : TopCat.{u}} (i : K ⟶ L)
    (f : parameterTensor E L ⟶ X.obj) :
    equivariantProductHomEquiv E X K (parameterTensorMap E i ≫ f) =
      parameterPrecompose i.hom (equivariantProductHomEquiv E X L f) := rfl

end

end DaggerOriginalEquivariantParameterTensor
