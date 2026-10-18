import OriginalSimplicialEquivariantParameterTensor

/-!
# The original realization-singular hom equivalence on equivariant maps

The native adjunction restricts to the original equivariance equations. The realization and
singular actions are exactly the native functors on the original group action. Naturality
retains the original equivariant source and target maps.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalSimplicialEquivariantParameterTensor

universe u

namespace DaggerOriginalEquivariantRealizationSingularHomEquiv

noncomputable section

/-- The native adjunction on the original equivariant hom sets. -/
def equivariantRealizationSingularHomEquiv (E : Action SSet.{u} C2.{u})
    (X : ContAction TopCat.{u} C2.{u}) :
    (E ⟶ singularAction X) ≃ ((SSet.toTop.mapAction C2.{u}).obj E ⟶ X.obj) where
  toFun q :=
    { hom := (sSetTopAdj.homEquiv E.V X.obj.V).symm q.hom
      comm g := by
        change SSet.toTop.map (E.ρ g).asHom ≫ (sSetTopAdj.homEquiv E.V X.obj.V).symm q.hom =
          (sSetTopAdj.homEquiv E.V X.obj.V).symm q.hom ≫ (X.obj.ρ g).asHom
        rw [← sSetTopAdj.homEquiv_naturality_left_symm,
          ← sSetTopAdj.homEquiv_naturality_right_symm]
        exact congrArg (sSetTopAdj.homEquiv E.V X.obj.V).symm (q.comm g) }
  invFun q :=
    { hom := sSetTopAdj.homEquiv E.V X.obj.V q.hom
      comm g := by
        change (E.ρ g).asHom ≫ sSetTopAdj.homEquiv E.V X.obj.V q.hom =
          sSetTopAdj.homEquiv E.V X.obj.V q.hom ≫ TopCat.toSSet.map (X.obj.ρ g).asHom
        rw [← sSetTopAdj.homEquiv_naturality_left, ← sSetTopAdj.homEquiv_naturality_right]
        exact congrArg (sSetTopAdj.homEquiv E.V X.obj.V) (q.comm g) }
  left_inv q := by
    apply Action.Hom.ext
    exact (sSetTopAdj.homEquiv E.V X.obj.V).apply_symm_apply q.hom
  right_inv q := by
    apply Action.Hom.ext
    exact (sSetTopAdj.homEquiv E.V X.obj.V).symm_apply_apply q.hom

/-- The original realization hom equivalence retains the same actual source map. -/
theorem equivariantRealizationSingularHomEquiv_parameter_naturality
    {E F : Action SSet.{u} C2.{u}} (i : E ⟶ F)
    (X : ContAction TopCat.{u} C2.{u}) (q : F ⟶ singularAction X) :
    equivariantRealizationSingularHomEquiv E X (i ≫ q) =
      (SSet.toTop.mapAction C2.{u}).map i ≫ equivariantRealizationSingularHomEquiv F X q := by
  apply Action.Hom.ext
  exact sSetTopAdj.homEquiv_naturality_left_symm i.hom q.hom

/-- The same native hom equivalence retains the actual equivariant target postcomposition. -/
theorem equivariantRealizationSingularHomEquiv_target_naturality
    (E : Action SSet.{u} C2.{u}) {X Y : ContAction TopCat.{u} C2.{u}}
    (f : X ⟶ Y) (q : E ⟶ singularAction X) :
    equivariantRealizationSingularHomEquiv E Y (q ≫ singularActionMap f) =
      equivariantRealizationSingularHomEquiv E X q ≫ f.hom := by
  apply Action.Hom.ext
  exact sSetTopAdj.homEquiv_naturality_right_symm q.hom f.hom.hom

end

end DaggerOriginalEquivariantRealizationSingularHomEquiv
