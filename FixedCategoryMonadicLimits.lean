import FixedCategoryAdjunction
import FixedGraphStructural
import DaggerModels.DaggerSimplicialMonadicity
import Mathlib.CategoryTheory.Monad.Limits

/-! The specified split quotient, Beck monadicity and small limits on the original fixed-O
dagger simplicial categories. Every enrichment and graph map is restricted from an existing
full construction. No colimits beyond graph-split coequalizers or model claims are made. -/

open CategoryTheory Limits DaggerModels

universe u

namespace DaggerFixedCategoryMonadicLimits

noncomputable section

namespace SplitQuotient

variable {O : Type u} {A B : FixedDaggerSimplicialCat O} {f g : A ⟶ B}
  {Q : FixedDaggerSimplicialGraph O}
  {π : (FixedDaggerSimplicialCat.forgetGraph O).obj B ⟶ Q}
  (t : IsSplitCoequalizer ((FixedDaggerSimplicialCat.forgetGraph O).map f)
    ((FixedDaggerSimplicialCat.forgetGraph O).map g) π)

def normalizedSplit : IsSplitCoequalizer (DaggerSimplicialCat.forgetGraph.map f.val)
    (DaggerSimplicialCat.forgetGraph.map g.val) (FixedDaggerSimplicialGraph.toGraphMap π) where
  rightSection := FixedDaggerSimplicialGraph.toGraphMap t.rightSection
  leftSection := FixedDaggerSimplicialGraph.toGraphMap t.leftSection
  condition := by
    simpa only [Functor.map_comp, FixedDaggerSimplicialGraph.forget,
      FixedDaggerSimplicialCat.forgetGraph_toGraph_map] using
        congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map t.condition
  rightSection_π := by
    simpa only [Functor.map_comp, Functor.map_id, FixedDaggerSimplicialGraph.forget] using
      congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map t.rightSection_π
  leftSection_bottom := by
    simpa only [Functor.map_comp, Functor.map_id, FixedDaggerSimplicialGraph.forget,
      FixedDaggerSimplicialCat.forgetGraph_toGraph_map] using
        congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map t.leftSection_bottom
  leftSection_top := by
    simpa only [Functor.map_comp, FixedDaggerSimplicialGraph.forget,
      FixedDaggerSimplicialCat.forgetGraph_toGraph_map] using
        congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map t.leftSection_top

def graphSplitData : DaggerSimplicialCat.SplitCoequalizer.GraphSplitData f.val g.val
    (FixedDaggerSimplicialGraph.toGraphMap π) :=
  DaggerSimplicialCat.SplitCoequalizer.GraphSplitData.ofMathlib (normalizedSplit t)

def point : FixedDaggerSimplicialCat O where
  enriched := DaggerSimplicialCat.SplitCoequalizer.quotientEnrichedCategory (graphSplitData t)
  daggerStructure := DaggerSimplicialCat.SplitCoequalizer.quotientDaggerStructure (graphSplitData t)

theorem point_toCat : (point t).toCat =
    DaggerSimplicialCat.SplitCoequalizer.quotientCategory (graphSplitData t) := rfl

theorem underlying_point : (FixedDaggerSimplicialCat.forgetGraph O).obj (point t) = Q := rfl

def quotientArrow : B ⟶ point t :=
  ⟨DaggerSimplicialCat.SplitCoequalizer.quotientFunctor (graphSplitData t), rfl⟩

theorem quotientArrow_toCat : (quotientArrow t).val =
    DaggerSimplicialCat.SplitCoequalizer.quotientFunctor (graphSplitData t) := rfl

theorem underlying_quotientArrow :
    (FixedDaggerSimplicialCat.forgetGraph O).map (quotientArrow t) = π := by
  apply FixedDaggerSimplicialCat.graph_map_injective
  rw [FixedDaggerSimplicialCat.forgetGraph_toGraph_map]
  rfl

theorem condition : f ≫ quotientArrow t = g ≫ quotientArrow t :=
  Subtype.ext (DaggerSimplicialCat.SplitCoequalizer.quotient_condition (graphSplitData t))

def cofork : Cofork f g := Cofork.ofπ (quotientArrow t) (condition t)

def ambientCofork (c : Cofork f g) : Cofork f.val g.val :=
  Cofork.ofπ c.π.val (congrArg Subtype.val c.condition)

def ambientDesc (c : Cofork f g) : (point t).toCat ⟶ c.pt.toCat :=
  (DaggerSimplicialCat.SplitCoequalizer.quotientIsColimit (graphSplitData t)).desc
    (ambientCofork c)

theorem ambientDesc_obj (c : Cofork f g) : (ambientDesc t c).obj = id := by
  change ((FixedDaggerSimplicialGraph.toGraphMap t.rightSection) ≫
    DaggerSimplicialCat.forgetGraph.map c.π.val).obj = id
  exact c.π.property

def desc (c : Cofork f g) : point t ⟶ c.pt := ⟨ambientDesc t c, ambientDesc_obj t c⟩

theorem desc_toCat (c : Cofork f g) : (desc t c).val = ambientDesc t c := rfl

theorem underlying_desc (c : Cofork f g) :
    DaggerSimplicialCat.forgetGraph.map (desc t c).val =
      FixedDaggerSimplicialGraph.toGraphMap t.rightSection ≫
        DaggerSimplicialCat.forgetGraph.map c.π.val := rfl

theorem fac (c : Cofork f g) : quotientArrow t ≫ desc t c = c.π := by
  apply Subtype.ext
  exact Cofork.IsColimit.π_desc
    (DaggerSimplicialCat.SplitCoequalizer.quotientIsColimit (graphSplitData t))
    (t := ambientCofork c)

theorem uniq (c : Cofork f g) (m : point t ⟶ c.pt)
    (hm : quotientArrow t ≫ m = c.π) : m = desc t c := by
  apply Subtype.ext
  exact Cofork.IsColimit.hom_ext
    (DaggerSimplicialCat.SplitCoequalizer.quotientIsColimit (graphSplitData t))
    ((congrArg Subtype.val hm).trans (congrArg Subtype.val (fac t c)).symm)

def isColimit : IsColimit (cofork t) :=
  Cofork.IsColimit.mk' _ (fun c ↦ ⟨desc t c, fac t c, fun hm ↦ uniq t c _ hm⟩)

def graphSplit : IsSplitCoequalizer ((FixedDaggerSimplicialCat.forgetGraph O).map f)
    ((FixedDaggerSimplicialCat.forgetGraph O).map g)
    ((FixedDaggerSimplicialCat.forgetGraph O).map (quotientArrow t)) := by
  simpa only [underlying_quotientArrow] using t

def preservesColimit : PreservesColimit (parallelPair f g)
    (FixedDaggerSimplicialCat.forgetGraph O) :=
  preservesColimit_of_preserves_colimit_cocone (isColimit t)
    ((isColimitMapCoconeCoforkEquiv (FixedDaggerSimplicialCat.forgetGraph O)
      (condition t)).symm (graphSplit t).isCoequalizer)

end SplitQuotient

variable {O : Type u}

def inverseOfGraphInverse {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D)
    (g : (FixedDaggerSimplicialCat.forgetGraph O).obj D ⟶
      (FixedDaggerSimplicialCat.forgetGraph O).obj C)
    (hfg : (FixedDaggerSimplicialCat.forgetGraph O).map f ≫ g = 𝟙 _)
    (hgf : g ≫ (FixedDaggerSimplicialCat.forgetGraph O).map f = 𝟙 _) : D ⟶ C :=
  ⟨DaggerSimplicialCat.inverseOfGraphInverse f.val
    (FixedDaggerSimplicialGraph.toGraphMap g)
    (by simpa only [Functor.map_comp, Functor.map_id, FixedDaggerSimplicialGraph.forget,
      FixedDaggerSimplicialCat.forgetGraph_toGraph_map] using
        congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map hfg)
    (by simpa only [Functor.map_comp, Functor.map_id, FixedDaggerSimplicialGraph.forget,
      FixedDaggerSimplicialCat.forgetGraph_toGraph_map] using
        congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map hgf), rfl⟩

theorem underlying_inverseOfGraphInverse {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D)
    (g : (FixedDaggerSimplicialCat.forgetGraph O).obj D ⟶
      (FixedDaggerSimplicialCat.forgetGraph O).obj C)
    (hfg : (FixedDaggerSimplicialCat.forgetGraph O).map f ≫ g = 𝟙 _)
    (hgf : g ≫ (FixedDaggerSimplicialCat.forgetGraph O).map f = 𝟙 _) :
    (FixedDaggerSimplicialCat.forgetGraph O).map (inverseOfGraphInverse f g hfg hgf) = g := by
  apply FixedDaggerSimplicialCat.graph_map_injective
  rw [FixedDaggerSimplicialCat.forgetGraph_toGraph_map]
  rfl

theorem comp_inverseOfGraphInverse {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D)
    (g : (FixedDaggerSimplicialCat.forgetGraph O).obj D ⟶
      (FixedDaggerSimplicialCat.forgetGraph O).obj C)
    (hfg : (FixedDaggerSimplicialCat.forgetGraph O).map f ≫ g = 𝟙 _)
    (hgf : g ≫ (FixedDaggerSimplicialCat.forgetGraph O).map f = 𝟙 _) :
    f ≫ inverseOfGraphInverse f g hfg hgf = 𝟙 C := by
  apply Subtype.ext
  apply DaggerSimplicialCat.forgetGraph.map_injective
  change DaggerSimplicialCat.forgetGraph.map f.val ≫
    FixedDaggerSimplicialGraph.toGraphMap g = 𝟙 _
  simpa only [Functor.map_comp, Functor.map_id, FixedDaggerSimplicialGraph.forget,
    FixedDaggerSimplicialCat.forgetGraph_toGraph_map] using
      congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map hfg

theorem inverseOfGraphInverse_comp {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D)
    (g : (FixedDaggerSimplicialCat.forgetGraph O).obj D ⟶
      (FixedDaggerSimplicialCat.forgetGraph O).obj C)
    (hfg : (FixedDaggerSimplicialCat.forgetGraph O).map f ≫ g = 𝟙 _)
    (hgf : g ≫ (FixedDaggerSimplicialCat.forgetGraph O).map f = 𝟙 _) :
    inverseOfGraphInverse f g hfg hgf ≫ f = 𝟙 D := by
  apply Subtype.ext
  apply DaggerSimplicialCat.forgetGraph.map_injective
  change FixedDaggerSimplicialGraph.toGraphMap g ≫
    DaggerSimplicialCat.forgetGraph.map f.val = 𝟙 _
  simpa only [Functor.map_comp, Functor.map_id, FixedDaggerSimplicialGraph.forget,
    FixedDaggerSimplicialCat.forgetGraph_toGraph_map] using
      congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map hgf

instance forgetGraphReflectsIsomorphisms :
    (FixedDaggerSimplicialCat.forgetGraph O).ReflectsIsomorphisms where
  reflects f :=
    ⟨inverseOfGraphInverse f (inv ((FixedDaggerSimplicialCat.forgetGraph O).map f))
      (IsIso.hom_inv_id _) (IsIso.inv_hom_id _), comp_inverseOfGraphInverse f _ _ _,
      inverseOfGraphInverse_comp f _ _ _⟩

instance hasCoequalizerOfIsSplitPair :
    Monad.HasCoequalizerOfIsSplitPair (FixedDaggerSimplicialCat.forgetGraph O) where
  out f g :=
    let t := HasSplitCoequalizer.isSplitCoequalizer
      ((FixedDaggerSimplicialCat.forgetGraph O).map f)
      ((FixedDaggerSimplicialCat.forgetGraph O).map g)
    HasColimit.mk ⟨SplitQuotient.cofork t, SplitQuotient.isColimit t⟩

instance preservesColimitOfIsSplitPair :
    Monad.PreservesColimitOfIsSplitPair (FixedDaggerSimplicialCat.forgetGraph O) where
  out f g :=
    SplitQuotient.preservesColimit (HasSplitCoequalizer.isSplitCoequalizer
      ((FixedDaggerSimplicialCat.forgetGraph O).map f)
      ((FixedDaggerSimplicialCat.forgetGraph O).map g))

instance monadicRightAdjoint : MonadicRightAdjoint (FixedDaggerSimplicialCat.forgetGraph O) :=
  Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms
    (DaggerFixedCategoryAdjunction.adjunction O)

theorem monadicLeftAdjoint_eq_free :
    monadicLeftAdjoint (FixedDaggerSimplicialCat.forgetGraph O) =
      DaggerFixedCategoryAdjunction.free O := rfl

theorem monadicAdjunction_eq_adjunction :
    monadicAdjunction (FixedDaggerSimplicialCat.forgetGraph O) =
      DaggerFixedCategoryAdjunction.adjunction O := rfl

instance createsSmallLimits :
    CreatesLimitsOfSize.{u, u} (FixedDaggerSimplicialCat.forgetGraph O) :=
  monadicCreatesLimits _

instance hasSmallLimits : HasLimitsOfSize.{u, u} (FixedDaggerSimplicialCat O) :=
  hasLimits_of_hasLimits_createsLimits (FixedDaggerSimplicialCat.forgetGraph O)

instance preservesSmallLimits :
    PreservesLimitsOfSize.{u, u} (FixedDaggerSimplicialCat.forgetGraph O) := inferInstance

instance reflectsSmallLimits :
    ReflectsLimitsOfSize.{u, u} (FixedDaggerSimplicialCat.forgetGraph O) := inferInstance

variable {J : Type u} [SmallCategory J] {K : J ⥤ FixedDaggerSimplicialCat O}
  {c : Cone (K ⋙ FixedDaggerSimplicialCat.forgetGraph O)} (hc : IsLimit c)

def liftedCone : Cone K := liftLimit hc

def validLift : (FixedDaggerSimplicialCat.forgetGraph O).mapCone (liftedCone hc) ≅ c :=
  liftedLimitMapsToOriginal hc

def liftedConeIsLimit : IsLimit (liftedCone hc) := liftedLimitIsLimit hc

theorem validLift_hom_leg (j : J) :
    (validLift hc).hom.hom ≫ c.π.app j =
      (FixedDaggerSimplicialCat.forgetGraph O).map ((liftedCone hc).π.app j) :=
  liftedLimitMapsToOriginal_hom_π hc j

theorem validLift_inv_leg (j : J) :
    (validLift hc).inv.hom ≫
      (FixedDaggerSimplicialCat.forgetGraph O).map ((liftedCone hc).π.app j) = c.π.app j :=
  liftedLimitMapsToOriginal_inv_map_π hc j

end

end DaggerFixedCategoryMonadicLimits
