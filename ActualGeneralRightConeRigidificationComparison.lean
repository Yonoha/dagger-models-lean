import ActualGeneralRightConeRigidificationLeg

/-! The actual original-Q comparison to original rigidification Homs, for EVERY simplicial input. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualGeneralRightConeMapping DaggerActualGeneralRightConeRigidificationLeg
universe u
namespace DaggerActualGeneralRightConeRigidificationComparison
noncomputable section
variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

def toSingular : rightMapping X a b ⟶ singular.obj (originalHom X a b) where
  app q σ := ULift.up (leg X a b q.unop σ)
  naturality q r α := by
    funext σ
    apply ULift.ext
    exact leg_precomp X a b α.unop σ

theorem toSingular_app (q : SimplexCategoryᵒᵖ) (σ : (rightMapping X a b).obj q) :
    ((toSingular X a b).app q σ).down = leg X a b q.unop σ := rfl

theorem toSingular_naturality {Y : SSet.{u}} (f : X ⟶ Y) :
    DaggerActualGeneralRightConeMapping.map f a b ≫
        toSingular Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) =
      toSingular X a b ≫ singular.map (homMap X a b f) := by
  apply NatTrans.ext
  funext q σ
  apply ULift.ext
  exact leg_postcomp X a b f q.unop σ

def toRealization : realization.obj (rightMapping X a b) ⟶ originalHom X a b :=
  (realizationSingularAdjunction.homEquiv _ _).symm (toSingular X a b)

theorem toRealization_adjunct :
    realizationSingularAdjunction.homEquiv _ _ (toRealization X a b) = toSingular X a b :=
  Equiv.apply_symm_apply _ _

theorem toRealization_naturality {Y : SSet.{u}} (f : X ⟶ Y) :
    realization.map (DaggerActualGeneralRightConeMapping.map f a b) ≫
        toRealization Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) =
      toRealization X a b ≫ homMap X a b f := by
  calc
    _ = (realizationSingularAdjunction.homEquiv _ _).symm
        (DaggerActualGeneralRightConeMapping.map f a b ≫
          toSingular Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)) :=
      (realizationSingularAdjunction.homEquiv_naturality_left_symm _ _).symm
    _ = (realizationSingularAdjunction.homEquiv _ _).symm
        (toSingular X a b ≫ singular.map (homMap X a b f)) :=
      congrArg (realizationSingularAdjunction.homEquiv _ _).symm
        (toSingular_naturality X a b f)
    _ = _ := realizationSingularAdjunction.homEquiv_naturality_right_symm _ _

theorem toRealization_on_simplex (q : SimplexCategory)
    (σ : (rightMapping X a b).obj (op q)) :
    realizationUnit.app q ≫ realization.map (uliftYonedaEquiv.symm σ) ≫
        toRealization X a b = leg X a b q σ := by
  have h := congrArg ULift.down
    (congrFun (NatTrans.congr_app (toRealization_adjunct X a b) (op q)) σ)
  change (((Presheaf.uliftYonedaAdjunction.{u}
    (uliftYoneda.{u}.leftKanExtension DaggerOriginalCounitRightConeQFunctor.QFunctor.{u})
    (uliftYoneda.{u}.leftKanExtensionUnit
      DaggerOriginalCounitRightConeQFunctor.QFunctor.{u})).homEquiv _ _
      (toRealization X a b)).app (op q) σ).down = leg X a b q σ at h
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app] at h
  exact h

theorem toRealization_leg (σ : SimplexIndex (rightMapping X a b)) :
    realizationUnit.app σ.left ≫ realization.map σ.hom ≫ toRealization X a b =
      leg X a b σ.left (uliftYonedaEquiv σ.hom) := by
  simpa only [Equiv.symm_apply_apply] using
    toRealization_on_simplex X a b σ.left (uliftYonedaEquiv σ.hom)

theorem toRealization_unique (g : realization.obj (rightMapping X a b) ⟶ originalHom X a b)
    (hg : ∀ σ : SimplexIndex (rightMapping X a b),
      realizationUnit.app σ.left ≫ realization.map σ.hom ≫ g =
        leg X a b σ.left (uliftYonedaEquiv σ.hom)) : g = toRealization X a b := by
  apply (simplexCoconeIsColimit (rightMapping X a b)).hom_ext
  intro σ
  change (realizationUnit.app σ.left ≫ realization.map σ.hom) ≫ g =
    (realizationUnit.app σ.left ≫ realization.map σ.hom) ≫ toRealization X a b
  rw [Category.assoc, Category.assoc, hg, toRealization_leg]

theorem toRealization_counit_factor :
    realization.map (toSingular X a b) ≫
        realizationSingularAdjunction.counit.app (originalHom X a b) =
      toRealization X a b :=
  (realizationSingularAdjunction.homEquiv_counit (g := toSingular X a b)).symm

end
end DaggerActualGeneralRightConeRigidificationComparison
