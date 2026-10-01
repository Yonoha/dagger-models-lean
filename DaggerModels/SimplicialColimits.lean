import DaggerModels.SimplicialColimitKernel
import DaggerModels.SimplicialHomQuotient

/-! Actual ordinary simplicial-category colimits, with arbitrary
object maps. Only the Type object colimit, free finite paths, and hom quotient
are used. No dagger or ordinary colimit existence premise is supplied. -/

open CategoryTheory Limits MonoidalCategory

universe u

namespace DaggerModels.SimplicialCat.SemanticColimit

variable {J : Type u} [SmallCategory J] (K : J ⥤ SimplicialCat.{u, u})


/-- The semantic kernel is stable under the original ordinary simplex operators. -/
noncomputable def relation : HomQuotient.StableHomRel (ColimitKernel.free K) where
  rel := ColimitKernel.rel K
  map_rel {_n _m} α {x y} {_f _g} h := ColimitKernel.rel_map K α x y h

/-- Quotient the free category after the Type colimit has identified its vertices. -/
noncomputable def point : SimplicialCat.{u, u} :=
  HomQuotient.quotientCategory (relation K)

noncomputable def quotient : ColimitKernel.free K ⟶ point K :=
  HomQuotient.quotientFunctor (relation K)

/-- The graph legs preserve enriched operations after passing to the quotient. -/
noncomputable def leg (j : J) : K.obj j ⟶ point K where
  obj := (ColimitKernel.leg K j).obj
  map X Y := (ColimitKernel.leg K j).map X Y ≫ (quotient K).map _ _
  map_id X := by
    ext n p
    cases p
    change HomQuotient.mk (relation K) n _ = HomQuotient.mk (relation K) n _
    exact HomQuotient.sound (relation K) n (ColimitKernel.rel_id K j n X)
  map_comp X Y Z := by
    ext n p
    rcases p with ⟨f, g⟩
    simp only [SSet.comp_app]
    change HomQuotient.mk (relation K) n _ = HomQuotient.mk (relation K) n _
    exact HomQuotient.sound (relation K) n (ColimitKernel.rel_comp K j n X Y Z f g)

theorem underlying_leg (j : J) : graphForget.map (leg K j) =
    ColimitKernel.leg K j ≫ graphForget.map (quotient K) := rfl

theorem leg_naturality {i j : J} (a : i ⟶ j) : K.map a ≫ leg K j = leg K i := by
  apply EnrichedFunctor.ext SSet
    (F := K.map a ≫ leg K j) (G := leg K i)
    (fun x ↦ ColimitKernel.vertexι_naturality K a x)
  intro x y
  ext n f
  change (((K.map a).map x y ≫ (ColimitKernel.leg K j).map _ _) ≫
      ((quotient K).map (ColimitKernel.vertexι K j ((K.map a).obj x))
        (ColimitKernel.vertexι K j ((K.map a).obj y)) ≫ eqToHom _)).app n f =
    ((ColimitKernel.leg K i).map x y ≫ (quotient K).map _ _).app n f
  rw [← ColimitKernel.map_cast (quotient K)
    (ColimitKernel.vertexι_naturality K a x) (ColimitKernel.vertexι_naturality K a y)]
  change HomQuotient.mk (relation K) n
      (((K.map a).map x y ≫ (ColimitKernel.leg K j).map _ _ ≫
        ColimitKernel.legTransport K a x y).app n f) =
    HomQuotient.mk (relation K) n (((ColimitKernel.leg K i).map x y).app n f)
  exact HomQuotient.sound (relation K) n (ColimitKernel.rel_naturality K a n x y f)

/-- The actual ordinary enriched cocone on the original diagram. -/
noncomputable def cocone : Cocone K where
  pt := point K
  ι :=
    { app := leg K
      naturality := by
        intro i j a
        simpa only [Functor.const_obj_map, Category.comp_id] using leg_naturality K a }

/-- Every original cocone kills the relation by the definition of its semantic kernel. -/
theorem kills (s : Cocone K) :
    HomQuotient.Kills (relation K) (ColimitKernel.freeLift K s) :=
  fun _ _ _ _ _ h ↦ h s

noncomputable def desc (s : Cocone K) : point K ⟶ s.pt :=
  HomQuotient.descend (relation K) (ColimitKernel.freeLift K s) (kills K s)

theorem quotient_desc (s : Cocone K) :
    quotient K ≫ desc K s = ColimitKernel.freeLift K s :=
  HomQuotient.quotientFunctor_descend (relation K) _ _

theorem leg_desc (s : Cocone K) (j : J) : leg K j ≫ desc K s = s.ι.app j := by
  apply graphForget.map_injective
  rw [Functor.map_comp, underlying_leg, Category.assoc, ← Functor.map_comp,
    quotient_desc, ColimitKernel.leg_freeLift]

/-- Equality of cocone legs determines all object images. -/
theorem desc_object_eq (s : Cocone K) (m : point K ⟶ s.pt)
    (hm : ∀ j, leg K j ≫ m = s.ι.app j) : m.obj = ColimitKernel.vertexDesc K s := by
  apply colimit.hom_ext (F := K ⋙ objects)
  intro j
  funext x
  exact (congrArg (fun F : K.obj j ⟶ s.pt ↦ F.obj x) (hm j)).trans
    (ColimitKernel.vertexDesc_ι K s j x).symm

/-- Every generating edge occurs in an original cocone leg. -/
theorem free_desc_unique (s : Cocone K) (m : point K ⟶ s.pt)
    (hm : ∀ j, leg K j ≫ m = s.ι.app j) :
    quotient K ≫ m = ColimitKernel.freeLift K s := by
  apply (SimplicialColimitsFree.homEquiv (ColimitKernel.graph K) s.pt).injective
  change SimplicialColimitsFree.restrict (quotient K ≫ m) =
    SimplicialColimitsFree.restrict (SimplicialColimitsFree.lift (ColimitKernel.edgeAssignment K s))
  rw [SimplicialColimitsFree.restrict_lift]
  apply SimplicialGraph.Map.ext' (fun x ↦ congrFun (desc_object_eq K s m hm) x)
  intro a b
  ext n e
  rcases e with ⟨⟨j, x, y, f⟩, hx, hy⟩
  change ColimitKernel.vertexι K j x = a at hx
  change ColimitKernel.vertexι K j y = b at hy
  subst a
  subst b
  have h := SimplicialGraph.Map.congr_map (congrArg graphForget.map (hm j)) x y
  have he := congrFun (NatTrans.congr_app h n) f
  have hcast : ((s.ι.app j).obj x ⟶[SSet] (s.ι.app j).obj y) =
      (ColimitKernel.vertexDesc K s (ColimitKernel.vertexι K j x) ⟶[SSet]
      ColimitKernel.vertexDesc K s (ColimitKernel.vertexι K j y)) := by
    rw [ColimitKernel.vertexDesc_ι, ColimitKernel.vertexDesc_ι]
  have he' := congrArg (fun p ↦ (eqToHom hcast).app n p) he
  have hmcast : ((leg K j ≫ m).obj x ⟶[SSet] (leg K j ≫ m).obj y) =
      ((s.ι.app j).obj x ⟶[SSet] (s.ι.app j).obj y) := by rw [hm j]
  change ((leg K j ≫ m).map x y ≫ eqToHom hmcast ≫ eqToHom hcast).app n f =
    ((s.ι.app j).map x y ≫ eqToHom hcast).app n f at he'
  rw [eqToHom_trans] at he'
  exact he'

/-- Uniqueness follows from the actual quotient and free-path universal properties. -/
theorem desc_unique (s : Cocone K) (m : point K ⟶ s.pt)
    (hm : ∀ j, leg K j ≫ m = s.ι.app j) : m = desc K s := by
  apply HomQuotient.quotientFunctor_precomp_injective (relation K)
  change quotient K ≫ m = quotient K ≫ desc K s
  rw [quotient_desc]
  exact free_desc_unique K s m hm

/-- The constructed cocone is the actual colimit of the arbitrary original diagram. -/
noncomputable def isColimit : IsColimit (cocone K) where
  desc := desc K
  fac := leg_desc K
  uniq := desc_unique K

theorem hasColimit : HasColimit K := ⟨⟨{ cocone := cocone K, isColimit := isColimit K }⟩⟩

/-- All diagrams at the common value universe have their constructed colimits. -/
theorem simplicialCatHasColimits :
    HasColimitsOfSize.{u, u} SimplicialCat.{u, u} := by
  constructor
  intro J _
  constructor
  intro K
  exact hasColimit K

end DaggerModels.SimplicialCat.SemanticColimit

namespace DaggerModels
/-- All ordinary small simplicial-category diagrams have their constructed colimits. -/
theorem simplicialCatHasColimits : HasColimits.{u} SimplicialCat.{u, u} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits
end DaggerModels
