import DaggerModels.DaggerHomQuotient
import DaggerModels.DaggerColimitKernel

/-! Construct actual small colimits using the semantic hom quotient.
Only graph colimits and the already constructed free adjunction are inputs. -/

open CategoryTheory Limits MonoidalCategory

universe u

namespace DaggerModels.DaggerSimplicialCat.SemanticColimit

variable {J : Type u} [SmallCategory J] (K : J ⥤ DaggerSimplicialCat.{u, u})

attribute [local instance] daggerGraphHasColimits

/-- The semantic kernel is stable under the original simplex operators and dagger. -/
noncomputable def relation : HomQuotient.StableHomRel (ColimitKernel.free K) where
  rel := ColimitKernel.rel K
  map_rel {_n _m} α {x y} {_f _g} h :=
    HomKernel.rel_map (fun s ↦ ColimitKernel.freeLift K s) α x y h
  dagger_rel {n x y _f _g} h :=
    HomKernel.rel_dagger (fun s ↦ ColimitKernel.freeLift K s) n x y h

/-- Quotient the free category after the graph colimit has identified its vertices. -/
noncomputable def point : DaggerSimplicialCat.{u, u} :=
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
  map_dagger X Y := (ColimitKernel.leg K j ≫ forgetGraph.map (quotient K)).map_dagger X Y

theorem underlying_leg (j : J) : forgetGraph.map (leg K j) =
    ColimitKernel.leg K j ≫ forgetGraph.map (quotient K) := rfl

theorem graph_leg_naturality {i j : J} (a : i ⟶ j) :
    forgetGraph.map (K.map a) ≫ ColimitKernel.leg K j = ColimitKernel.leg K i := by
  unfold ColimitKernel.leg
  change (K ⋙ forgetGraph).map a ≫ colimit.ι (K ⋙ forgetGraph) j ≫ _ = _
  rw [colimit.w_assoc]

theorem leg_naturality {i j : J} (a : i ⟶ j) : K.map a ≫ leg K j = leg K i := by
  apply forgetGraph.map_injective
  rw [Functor.map_comp, underlying_leg, underlying_leg, ← Category.assoc,
    graph_leg_naturality]

/-- The actual dagger enriched cocone on the original diagram. -/
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
  apply forgetGraph.map_injective
  rw [Functor.map_comp, underlying_leg, Category.assoc, ← Functor.map_comp,
    quotient_desc, ColimitKernel.leg_freeLift]

/-- Uniqueness follows from the quotient, free, and graph-colimit universal properties. -/
theorem desc_unique (s : Cocone K) (m : point K ⟶ s.pt)
    (hm : ∀ j, leg K j ≫ m = s.ι.app j) : m = desc K s := by
  apply HomQuotient.quotientFunctor_precomp_injective (relation K)
  change quotient K ≫ m = quotient K ≫ desc K s
  rw [quotient_desc]
  apply (FreeDaggerSimplicialCategory.homEquiv (ColimitKernel.graph K) s.pt).injective
  change FreeDaggerSimplicialCategory.unit (ColimitKernel.graph K) ≫
      forgetGraph.map (quotient K ≫ m) =
    FreeDaggerSimplicialCategory.unit (ColimitKernel.graph K) ≫
      forgetGraph.map (ColimitKernel.freeLift K s)
  apply colimit.hom_ext
  intro j
  rw [← Category.assoc, ← Category.assoc]
  change ColimitKernel.leg K j ≫ forgetGraph.map (quotient K ≫ m) =
    ColimitKernel.leg K j ≫ forgetGraph.map (ColimitKernel.freeLift K s)
  rw [ColimitKernel.leg_freeLift, Functor.map_comp, ← Category.assoc,
    ← underlying_leg, ← Functor.map_comp, hm]

/-- The constructed cocone is the actual colimit of the arbitrary original diagram. -/
noncomputable def isColimit : IsColimit (cocone K) where
  desc := desc K
  fac := leg_desc K
  uniq := desc_unique K

theorem hasColimit : HasColimit K := ⟨⟨{ cocone := cocone K, isColimit := isColimit K }⟩⟩

/-- All diagrams at the common value universe have their constructed colimits. -/
theorem daggerSimplicialCatHasColimits :
    HasColimitsOfSize.{u, u} DaggerSimplicialCat.{u, u} := by
  constructor
  intro J _
  constructor
  intro K
  exact hasColimit K

end DaggerModels.DaggerSimplicialCat.SemanticColimit
