import DaggerModels.SimplicialOpposite

/-! Recover the original mapping-space dagger from an identity-on-objects
involutive enriched functor to the ordinary opposite. This adapter is used in
the limit and colimit lifting constructions. -/

open CategoryTheory MonoidalCategory Opposite

universe o v

namespace DaggerModels.DaggerSimplicialStructure

noncomputable def ofOppositeFunctor (C : SimplicialCat.{o, v})
    (d : C ⟶ SimplicialCat.opposite C)
    (hobj : ∀ X, d.obj X = op X)
    (hinv : d ≫ SimplicialCat.oppositeMap d ≫ SimplicialCat.doubleOppositeHom C = 𝟙 C) :
    DaggerSimplicialStructure C.Obj := by
  rcases d with ⟨obj, maps, ids, comps⟩
  have h : obj = op := funext hobj
  subst obj
  refine { dagger := maps, dagger_involutive := ?_, dagger_id := ids, dagger_comp := comps }
  intro X Y
  exact eq_of_heq (congr_arg_heq (fun F : C ⟶ C ↦ F.map X Y) hinv)

end DaggerModels.DaggerSimplicialStructure

namespace DaggerModels.DaggerSimplicialStructure

/-- The adapter retains the entire original opposite functor. -/
theorem ofOppositeFunctor_daggerFunctor (C : SimplicialCat.{o, v})
    (d : C ⟶ SimplicialCat.opposite C) (hobj : ∀ X, d.obj X = op X)
    (hinv : d ≫ SimplicialCat.oppositeMap d ≫ SimplicialCat.doubleOppositeHom C = 𝟙 C) :
    @daggerFunctor C.Obj C.enriched (ofOppositeFunctor C d hobj hinv) = d := by
  rcases d with ⟨obj, maps, ids, comps⟩
  have h : obj = op := funext hobj
  subst obj
  rfl

end DaggerModels.DaggerSimplicialStructure

namespace DaggerModels.DaggerSimplicialCat

/-- The natural opposite map squares to the actual double-opposite identification. -/
theorem daggerNatural_square (C : DaggerSimplicialCat.{o, v}) :
    daggerNatural.app C ≫ SimplicialCat.oppositeMap (daggerNatural.app C) ≫
      SimplicialCat.doubleOppositeHom C.toSimplicialCat = 𝟙 C.toSimplicialCat := by
  change (daggerNatural.app C).comp SSet
      ((SimplicialCat.oppositeMap (daggerNatural.app C)).comp SSet
        (SimplicialCat.doubleOppositeHom C.toSimplicialCat)) =
    EnrichedFunctor.id SSet C.Obj
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro X
    rfl
  case h_map =>
    intro X Y
    simpa [daggerNatural, SimplicialCat.oppositeMap, SimplicialCat.doubleOppositeHom,
      DaggerSimplicialStructure.daggerFunctor, EnrichedFunctor.comp, EnrichedFunctor.id]
      using DaggerSimplicialStructure.dagger_involutive (C := C.Obj) X Y

end DaggerModels.DaggerSimplicialCat
