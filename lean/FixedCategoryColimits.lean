import FixedCategoryColimitKernel
import DaggerModels.DaggerHomQuotient

/-! All small colimits of the original fixed-object dagger simplicial categories.
The graph colimit, free paths, semantic hom quotient and every cocone map keep literal `O`.
No preservation of these colimits by the graph forgetful functor is asserted. -/

open CategoryTheory Limits DaggerModels

universe u

namespace DaggerFixedCategoryColimits

noncomputable section

variable {O : Type u} {J : Type u} [SmallCategory J] (K : J ⥤ FixedDaggerSimplicialCat O)

def point : FixedDaggerSimplicialCat O where
  enriched := DaggerSimplicialCat.HomQuotient.enrichedCategory (Kernel.relation K)
  daggerStructure := DaggerSimplicialCat.HomQuotient.daggerStructure (Kernel.relation K)

theorem point_toCat :
    (point K).toCat = DaggerSimplicialCat.HomQuotient.quotientCategory (Kernel.relation K) := rfl

def quotient : Kernel.free K ⟶ point K :=
  ⟨DaggerSimplicialCat.HomQuotient.quotientFunctor (Kernel.relation K), rfl⟩

def ambientLeg (j : J) : (K.obj j).toCat ⟶ (point K).toCat where
  obj := id
  map x y := (Kernel.leg K j).map x y ≫ (quotient K).val.map x y
  map_id x := by
    ext n p
    cases p
    change DaggerSimplicialCat.HomQuotient.mk (Kernel.relation K) n _ =
      DaggerSimplicialCat.HomQuotient.mk (Kernel.relation K) n _
    exact DaggerSimplicialCat.HomQuotient.sound (Kernel.relation K) n (Kernel.rel_id K j n x)
  map_comp x y z := by
    ext n p
    rcases p with ⟨f, g⟩
    simp only [SSet.comp_app]
    change DaggerSimplicialCat.HomQuotient.mk (Kernel.relation K) n _ =
      DaggerSimplicialCat.HomQuotient.mk (Kernel.relation K) n _
    exact DaggerSimplicialCat.HomQuotient.sound (Kernel.relation K) n
      (Kernel.rel_comp K j n x y z f g)
  map_dagger x y := (FixedDaggerSimplicialGraph.toGraphMap (Kernel.leg K j) ≫
    DaggerSimplicialCat.forgetGraph.map (quotient K).val).map_dagger x y

def leg (j : J) : K.obj j ⟶ point K := ⟨ambientLeg K j, rfl⟩

theorem underlying_leg (j : J) : DaggerSimplicialCat.forgetGraph.map (leg K j).val =
    FixedDaggerSimplicialGraph.toGraphMap (Kernel.leg K j) ≫
      DaggerSimplicialCat.forgetGraph.map (quotient K).val := rfl

theorem fixed_underlying_leg (j : J) :
    (FixedDaggerSimplicialCat.forgetGraph O).map (leg K j) =
      Kernel.leg K j ≫ (FixedDaggerSimplicialCat.forgetGraph O).map (quotient K) := by
  apply FixedDaggerSimplicialCat.graph_map_injective
  rw [FixedDaggerSimplicialCat.forgetGraph_toGraph_map]
  exact underlying_leg K j

theorem graph_leg_naturality {i j : J} (a : i ⟶ j) :
    (FixedDaggerSimplicialCat.forgetGraph O).map (K.map a) ≫ Kernel.leg K j =
      Kernel.leg K i := by
  unfold Kernel.leg
  change (K ⋙ FixedDaggerSimplicialCat.forgetGraph O).map a ≫
    colimit.ι (K ⋙ FixedDaggerSimplicialCat.forgetGraph O) j ≫ _ = _
  rw [colimit.w_assoc]

theorem leg_naturality {i j : J} (a : i ⟶ j) : K.map a ≫ leg K j = leg K i := by
  apply Subtype.ext
  apply DaggerSimplicialCat.forgetGraph.map_injective
  have h : (FixedDaggerSimplicialCat.forgetGraph O).map (K.map a ≫ leg K j) =
      (FixedDaggerSimplicialCat.forgetGraph O).map (leg K i) := by
    rw [Functor.map_comp, fixed_underlying_leg, fixed_underlying_leg,
      ← Category.assoc, graph_leg_naturality]
  simpa only [FixedDaggerSimplicialCat.forgetGraph_toGraph_map,
    FixedDaggerSimplicialCat.forget] using
      congrArg FixedDaggerSimplicialGraph.toGraphMap h

def cocone : Cocone K where
  pt := point K
  ι :=
    { app := leg K
      naturality := by
        intro i j a
        simpa only [Functor.const_obj_map, Category.comp_id] using leg_naturality K a }

theorem kills (s : Cocone K) :
    DaggerSimplicialCat.HomQuotient.Kills (Kernel.relation K) (Kernel.freeLift K s).val :=
  fun _ _ _ _ _ h ↦ h s

def desc (s : Cocone K) : point K ⟶ s.pt :=
  ⟨DaggerSimplicialCat.HomQuotient.descend (Kernel.relation K)
    (Kernel.freeLift K s).val (kills K s), (Kernel.freeLift K s).property⟩

theorem quotient_desc (s : Cocone K) : quotient K ≫ desc K s = Kernel.freeLift K s :=
  Subtype.ext (DaggerSimplicialCat.HomQuotient.quotientFunctor_descend (Kernel.relation K) _ _)

theorem leg_desc (s : Cocone K) (j : J) : leg K j ≫ desc K s = s.ι.app j := by
  apply Subtype.ext
  apply DaggerSimplicialCat.forgetGraph.map_injective
  have h : (FixedDaggerSimplicialCat.forgetGraph O).map (leg K j ≫ desc K s) =
      (FixedDaggerSimplicialCat.forgetGraph O).map (s.ι.app j) := by
    rw [Functor.map_comp, fixed_underlying_leg, Category.assoc, ← Functor.map_comp,
      quotient_desc, Kernel.leg_freeLift]
  simpa only [FixedDaggerSimplicialCat.forgetGraph_toGraph_map,
    FixedDaggerSimplicialCat.forget] using
      congrArg FixedDaggerSimplicialGraph.toGraphMap h

theorem desc_unique (s : Cocone K) (m : point K ⟶ s.pt)
    (hm : ∀ j, leg K j ≫ m = s.ι.app j) : m = desc K s := by
  apply Subtype.ext
  apply DaggerSimplicialCat.HomQuotient.quotientFunctor_precomp_injective (Kernel.relation K)
  have h : quotient K ≫ m = Kernel.freeLift K s := by
    apply ((DaggerFixedCategoryAdjunction.adjunction O).homEquiv (Kernel.graph K) s.pt).injective
    change (DaggerFixedCategoryAdjunction.adjunction O).unit.app (Kernel.graph K) ≫
        (FixedDaggerSimplicialCat.forgetGraph O).map (quotient K ≫ m) =
      (DaggerFixedCategoryAdjunction.adjunction O).unit.app (Kernel.graph K) ≫
        (FixedDaggerSimplicialCat.forgetGraph O).map (Kernel.freeLift K s)
    apply colimit.hom_ext
    intro j
    rw [← Category.assoc, ← Category.assoc]
    change Kernel.leg K j ≫ (FixedDaggerSimplicialCat.forgetGraph O).map (quotient K ≫ m) =
      Kernel.leg K j ≫ (FixedDaggerSimplicialCat.forgetGraph O).map (Kernel.freeLift K s)
    rw [Kernel.leg_freeLift, Functor.map_comp, ← Category.assoc,
      ← fixed_underlying_leg, ← Functor.map_comp, hm]
  exact (congrArg Subtype.val h).trans (congrArg Subtype.val (quotient_desc K s)).symm

def isColimit : IsColimit (cocone K) where
  desc := desc K
  fac := leg_desc K
  uniq := desc_unique K

theorem hasColimit : HasColimit K := ⟨⟨{ cocone := cocone K, isColimit := isColimit K }⟩⟩

instance hasSmallColimits : HasColimitsOfSize.{u, u} (FixedDaggerSimplicialCat O) := by
  constructor
  intro J _
  constructor
  intro K
  exact hasColimit K

end

end DaggerFixedCategoryColimits
