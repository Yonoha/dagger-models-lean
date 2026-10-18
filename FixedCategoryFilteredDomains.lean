import FixedCategoryMonadicLimits
import FixedGraphConnectedColimits
import FixedCategoryGenerators
import DaggerModels.FreeWordFinitary
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Filtered.Connected

/-! Filtered creation and finite presentability of the ORIGINAL free generator domains.
The same fixed word functor, adjunction and literal I/J families are used throughout. -/

open CategoryTheory Limits DaggerModels
open DaggerFixedCategoryAdjunction DaggerFixedGraphConnectedColimits

universe u

namespace DaggerFixedCategoryFilteredDomains

noncomputable section

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (O : Type u)

/-- The full original word square transfers every filtered-shape preservation. -/
instance fixedWordsPreservesFiltered (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (fixedWords O) := by
  letI : IsConnected J := IsFiltered.isConnected J
  letI : IsCardinalFiltered J Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff J).2 inferInstance
  letI : ambientWords.{u}.IsCardinalAccessible Cardinal.aleph0.{u} :=
    FreeWordFinitary.isCardinalAccessible
  letI : PreservesColimitsOfShape J ambientWords.{u} :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ Cardinal.aleph0 J
  letI : PreservesColimitsOfShape J
      (fixedWords O ⋙ FixedDaggerSimplicialGraph.forget) :=
    preservesColimitsOfShape_of_natIso (wordSquareIso O).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (fixedWords O) FixedDaggerSimplicialGraph.forget

instance fixedWordsIsCardinalAccessible :
    (fixedWords O).IsCardinalAccessible Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    letI : IsFiltered J := (isCardinalFiltered_aleph0_iff J).1 inferInstance
    exact fixedWordsPreservesFiltered O J

/-- Beck's chosen word functor is definitionally the same original F_O followed by U_O. -/
instance monadicWordsPreservesFiltered (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (monadicLeftAdjoint (FixedDaggerSimplicialCat.forgetGraph O) ⋙
        FixedDaggerSimplicialCat.forgetGraph O) := by
  change PreservesColimitsOfShape J (fixedWords O)
  exact fixedWordsPreservesFiltered O J

/-- BOTH preservation hypotheses follow from the global filtered-shape word result. -/
instance createsFilteredColimit (J : Type u) [SmallCategory J] [IsFiltered J]
    (K : J ⥤ FixedDaggerSimplicialCat O) :
    CreatesColimit K (FixedDaggerSimplicialCat.forgetGraph O) := by
  letI : PreservesColimit (K ⋙ FixedDaggerSimplicialCat.forgetGraph O)
      (monadicLeftAdjoint (FixedDaggerSimplicialCat.forgetGraph O) ⋙
        FixedDaggerSimplicialCat.forgetGraph O) := inferInstance
  letI : PreservesColimit ((K ⋙ FixedDaggerSimplicialCat.forgetGraph O) ⋙
        monadicLeftAdjoint (FixedDaggerSimplicialCat.forgetGraph O) ⋙
          FixedDaggerSimplicialCat.forgetGraph O)
      (monadicLeftAdjoint (FixedDaggerSimplicialCat.forgetGraph O) ⋙
        FixedDaggerSimplicialCat.forgetGraph O) := inferInstance
  exact monadicCreatesColimitOfPreservesColimit (FixedDaggerSimplicialCat.forgetGraph O) K

instance createsFilteredColimits (J : Type u) [SmallCategory J] [IsFiltered J] :
    CreatesColimitsOfShape J (FixedDaggerSimplicialCat.forgetGraph O) :=
  ⟨fun {K} ↦ createsFilteredColimit O J K⟩

instance hasFilteredColimits (J : Type u) [SmallCategory J] [IsFiltered J] :
    HasColimitsOfShape J (FixedDaggerSimplicialCat O) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (FixedDaggerSimplicialCat.forgetGraph O)

instance preservesFilteredColimits (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (FixedDaggerSimplicialCat.forgetGraph O) := inferInstance

instance reflectsFilteredColimits (J : Type u) [SmallCategory J] [IsFiltered J] :
    ReflectsColimitsOfShape J (FixedDaggerSimplicialCat.forgetGraph O) := inferInstance

instance forgetGraphIsCardinalAccessible :
    (FixedDaggerSimplicialCat.forgetGraph O).IsCardinalAccessible Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    letI : IsFiltered J := (isCardinalFiltered_aleph0_iff J).1 inferInstance
    exact preservesFilteredColimits O J

instance hasCardinalFilteredColimits :
    HasCardinalFilteredColimits (FixedDaggerSimplicialCat O) Cardinal.aleph0.{u} where
  hasColimitsOfShape J _ _ := by
    letI : IsFiltered J := (isCardinalFiltered_aleph0_iff J).1 inferInstance
    exact hasFilteredColimits O J

variable {O} {J : Type u} [SmallCategory J] [IsFiltered J]
  {K : J ⥤ FixedDaggerSimplicialCat O}
  {c : Cocone (K ⋙ FixedDaggerSimplicialCat.forgetGraph O)} (hc : IsColimit c)

def liftedCocone : Cocone K := liftColimit hc

def validLift : (FixedDaggerSimplicialCat.forgetGraph O).mapCocone (liftedCocone hc) ≅ c :=
  liftedColimitMapsToOriginal hc

def liftedCoconeIsColimit : IsColimit (liftedCocone hc) := liftedColimitIsColimit hc

theorem validLift_hom_leg (j : J) :
    (FixedDaggerSimplicialCat.forgetGraph O).map ((liftedCocone hc).ι.app j) ≫
      (validLift hc).hom.hom = c.ι.app j := (validLift hc).hom.w j

theorem validLift_inv_leg (j : J) :
    c.ι.app j ≫ (validLift hc).inv.hom =
      (FixedDaggerSimplicialCat.forgetGraph O).map ((liftedCocone hc).ι.app j) :=
  (validLift hc).inv.w j

variable (O)

theorem free_obj_isFinitelyPresentable (G : FixedDaggerSimplicialGraph O)
    [IsFinitelyPresentable.{u} G] : IsFinitelyPresentable.{u} ((free O).obj G) :=
  (adjunction O).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 G

theorem free_I_domain_isFinitelyPresentable {G H : FixedDaggerSimplicialGraph O}
    (i : G ⟶ H) (hi : DaggerFixedGraphGenerators.I O i) :
    IsFinitelyPresentable.{u} ((free O).obj G) := by
  letI := DaggerFixedGraphGenerators.I_domain_isFinitelyPresentable O i hi
  exact free_obj_isFinitelyPresentable O G

theorem free_J_domain_isFinitelyPresentable {G H : FixedDaggerSimplicialGraph O}
    (i : G ⟶ H) (hi : DaggerFixedGraphGenerators.J O i) :
    IsFinitelyPresentable.{u} ((free O).obj G) := by
  letI := DaggerFixedGraphGenerators.J_domain_isFinitelyPresentable O i hi
  exact free_obj_isFinitelyPresentable O G

theorem I_domain_isFinitelyPresentable {C D : FixedDaggerSimplicialCat O}
    (i : C ⟶ D) (hi : DaggerFixedCategoryGenerators.I O i) : IsFinitelyPresentable.{u} C := by
  cases hi with
  | mk k =>
    exact free_I_domain_isFinitelyPresentable O
      ((DaggerFixedGraphGenerators.placement O k.1).map (SSet.boundary.{u} k.2).ι) (.mk k)

theorem J_domain_isFinitelyPresentable {C D : FixedDaggerSimplicialCat O}
    (i : C ⟶ D) (hi : DaggerFixedCategoryGenerators.J O i) : IsFinitelyPresentable.{u} C := by
  cases hi with
  | mk k =>
    exact free_J_domain_isFinitelyPresentable O
      ((DaggerFixedGraphGenerators.placement O k.1).map
        (SSet.horn.{u} (k.2.1 + 1) k.2.2).ι) (.mk k)

end

end DaggerFixedCategoryFilteredDomains
