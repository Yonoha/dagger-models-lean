import OriginalOrdinaryKanCoreSubcomplex

/-!
# Functoriality of the ordinary core candidate

This restricts simplicial morphisms to the preimage of the literal nerve of
the categorical core. No Kan or maximality property is asserted.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalOrdinaryKanCoreSubcomplex

noncomputable section

/-- The actual homotopy-category morphism induced by a simplicial map. -/
def homotopyCategoryMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    (SSet.hoFunctor.obj X) ⥤ (SSet.hoFunctor.obj Y) :=
  (SSet.hoFunctor.map f).toFunctor

/-- The corresponding nerve map. -/
def nerveHomotopyCategoryMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    CategoryTheory.nerve (SSet.hoFunctor.obj X) ⟶
      CategoryTheory.nerve (SSet.hoFunctor.obj Y) :=
  CategoryTheory.nerveMap (homotopyCategoryMap f)

/-- The ordinary categorical core of the homotopy-category map. -/
def nerveCoreMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    CategoryTheory.nerve (CategoryTheory.Core (SSet.hoFunctor.obj X)) ⟶
      CategoryTheory.nerve (CategoryTheory.Core (SSet.hoFunctor.obj Y)) :=
  CategoryTheory.nerveMap (Functor.core (homotopyCategoryMap f))

/-- The actual unit is natural, with no quasi-category hypothesis. -/
theorem homotopyCategoryUnit_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ homotopyCategoryUnit Y =
      homotopyCategoryUnit X ≫ nerveHomotopyCategoryMap f := by
  exact CategoryTheory.nerveAdjunction.unit.naturality f

/-- Ordinary core inclusion commutes with the map induced by `f`. -/
theorem nerveCoreInclusion_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    nerveCoreMap f ≫ nerveCoreInclusion Y =
      nerveCoreInclusion X ≫ nerveHomotopyCategoryMap f := by
  change CategoryTheory.nerveMap
      ((homotopyCategoryMap f).core ⋙
        CategoryTheory.Core.inclusion (SSet.hoFunctor.obj Y)) =
    CategoryTheory.nerveMap
      (CategoryTheory.Core.inclusion (SSet.hoFunctor.obj X) ⋙
        homotopyCategoryMap f)
  rw [Functor.core_comp_inclusion]

/-- Every simplicial map restricts to the literal ordinary core candidate. -/
def ordinaryCoreCandidateMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ordinaryCoreCandidate X : SSet.{u}) ⟶
      (ordinaryCoreCandidate Y : SSet.{u}) where
  app n s := ⟨f.app n s.val, by
    obtain ⟨t, ht⟩ :=
      (mem_ordinaryCoreCandidate_iff X n s.val).1 s.property
    apply (mem_ordinaryCoreCandidate_iff Y n (f.app n s.val)).2
    refine ⟨(nerveCoreMap f).app n t, ?_⟩
    calc
      (nerveCoreInclusion Y).app n ((nerveCoreMap f).app n t) =
          (nerveHomotopyCategoryMap f).app n
            ((nerveCoreInclusion X).app n t) := by
        exact congrArg (fun g :
            CategoryTheory.nerve (CategoryTheory.Core (SSet.hoFunctor.obj X)) ⟶
              CategoryTheory.nerve (SSet.hoFunctor.obj Y) => g.app n t)
          (nerveCoreInclusion_natural f)
      _ = (nerveHomotopyCategoryMap f).app n
            ((homotopyCategoryUnit X).app n s.val) := by rw [ht]
      _ = (homotopyCategoryUnit Y).app n (f.app n s.val) := by
        exact congrArg (fun g : X ⟶
            CategoryTheory.nerve (SSet.hoFunctor.obj Y) => g.app n s.val)
          (homotopyCategoryUnit_natural f).symm⟩
  naturality m n g := by
    ext s
    apply Subtype.ext
    exact congrFun (f.naturality g) s.val

@[reassoc]
theorem ordinaryCoreCandidateMap_comp_ι {X Y : SSet.{u}} (f : X ⟶ Y) :
    ordinaryCoreCandidateMap f ≫ (ordinaryCoreCandidate Y).ι =
      (ordinaryCoreCandidate X).ι ≫ f := by
  rfl

end

end DaggerOriginalOrdinaryKanCoreSubcomplex
