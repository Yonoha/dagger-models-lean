import DaggerModels.FreeDaggerSimplicialCategory
import DaggerModels.DaggerHomKernel
import DaggerModels.DaggerHomQuotient
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Free daggers on an already composed simplicial category

The doubled graph retains the original objects. Its existing free path category
is quotiented by kernels of all actual enriched input functors into dagger targets.
The positive-generator unit therefore preserves the original identities and composition.
-/

open CategoryTheory MonoidalCategory

universe u

noncomputable section

namespace DaggerModels.OrdinaryFreeDagger

/-- Two directed copies of the original full hom spaces. -/
def doubledHom (C : SimplicialCat.{u, u}) (X Y : C.Obj) : SSet.{u} where
  obj n := Sum ((X ⟶[SSet] Y).obj n) ((Y ⟶[SSet] X).obj n)
  map α := Sum.map ((X ⟶[SSet] Y).map α) ((Y ⟶[SSet] X).map α)
  map_id n := by
    funext p
    cases p <;> simp
  map_comp α β := by
    funext p
    cases p <;> simp

/-- The ordinary hom dagger exchanges the directed tags, without simplex reversal. -/
def doubledDagger (C : SimplicialCat.{u, u}) (X Y : C.Obj) :
    doubledHom C X Y ⟶ doubledHom C Y X where
  app _ p := p.swap
  naturality {_n _m} α := by
    funext p
    cases p <;> rfl

/-- The original object type with formal forward and reverse edges. -/
def graph (C : SimplicialCat.{u, u}) : DaggerSimplicialGraph.{u} where
  Obj := C.Obj
  Hom := doubledHom C
  dagger := doubledDagger C
  dagger_involutive X Y := by
    ext n p
    cases p <;> rfl

/-- The original hom simplex as a positive directed generator. -/
def positive (C : SimplicialCat.{u, u}) (X Y : C.Obj) :
    (X ⟶[SSet] Y) ⟶ (graph C).Hom X Y where
  app _ := Sum.inl

/-- An original enriched functor determines the full doubled dagger graph map. -/
def assignment (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ DaggerSimplicialCat.forget.obj D) :
    graph C ⟶ DaggerSimplicialCat.forgetGraph.obj D where
  obj := F.obj
  map X Y :=
    { app n := Sum.elim ((F.map X Y).app n)
        ((F.map Y X ≫ DaggerSimplicialStructure.dagger (C := D.Obj)
          (F.obj Y) (F.obj X)).app n)
      naturality {_n _m} α := by
        funext p
        cases p with
        | inl f => exact congrFun ((F.map X Y).naturality α) f
        | inr f =>
          exact congrFun
            ((F.map Y X ≫ DaggerSimplicialStructure.dagger (C := D.Obj)
              (F.obj Y) (F.obj X)).naturality α) f }
  map_dagger X Y := by
    ext n p
    cases p with
    | inl f => rfl
    | inr f =>
      exact congrFun (NatTrans.congr_app
        (DaggerSimplicialStructure.dagger_involutive (C := D.Obj) (F.obj Y) (F.obj X)) n)
          ((F.map Y X).app n f)

/-- The already constructed finite-path dagger category of the doubled graph. -/
def free (C : SimplicialCat.{u, u}) : DaggerSimplicialCat.{u, u} :=
  FreeDaggerSimplicialCategory.functor.obj (graph C)

/-- Insert an original hom simplex as a positive singleton path. -/
def edge (C : SimplicialCat.{u, u}) (X Y : C.Obj) :
    (X ⟶[SSet] Y) ⟶ (DaggerSimplicialCat.underlyingGraph (free C)).Hom X Y :=
  positive C X Y ≫ (FreeDaggerSimplicialCategory.unit (graph C)).map X Y

/-- Evaluate the free paths using the actual original enriched input functor. -/
def evaluator (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ DaggerSimplicialCat.forget.obj D) : free C ⟶ D :=
  FreeDaggerSimplicialCategory.lift (assignment C F)

/-- Evaluation retains the entire original positive hom map. -/
theorem edge_evaluator (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ DaggerSimplicialCat.forget.obj D) (X Y : C.Obj) :
    edge C X Y ≫ (evaluator C F).map X Y = F.map X Y := by
  letI := FreeSimplicialPaths.enrichedCategory (graph C)
  change (positive C X Y ≫ FreeSimplicialPaths.inclusion (graph C) X Y) ≫
    (FreeSimplicialExtension.extend (graph C) F.obj (assignment C F).map).map X Y = _
  rw [Category.assoc, FreeSimplicialExtension.inclusion_extend]
  rfl

/-- Every simplex of the original positive hom map is retained. -/
theorem edge_evaluator_app (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ DaggerSimplicialCat.forget.obj D) (X Y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (f : (X ⟶[SSet] Y).obj n) :
    ((evaluator C F).map X Y).app n ((edge C X Y).app n f) =
      (F.map X Y).app n f :=
  congrFun (NatTrans.congr_app (edge_evaluator C F X Y) n) f

/-- The semantic family contains every actual original enriched input functor. -/
abbrev Model (C : SimplicialCat.{u, u}) :=
  Σ D : DaggerSimplicialCat.{u, u}, (C ⟶ DaggerSimplicialCat.forget.obj D)

/-- The full joint kernel stays proposition-valued despite the larger model family. -/
def rel (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (X Y : C.Obj)
    (f g : ((DaggerSimplicialCat.underlyingGraph (free C)).Hom X Y).obj n) : Prop :=
  DaggerSimplicialCat.HomKernel.rel (fun s : Model C ↦ evaluator C s.2) n X Y f g

/-- The actual kernel is stable under the original operators and hom dagger. -/
def relation (C : SimplicialCat.{u, u}) :
    DaggerSimplicialCat.HomQuotient.StableHomRel (free C) where
  rel := rel C
  map_rel {_n _m} α {X Y} {_f _g} h :=
    DaggerSimplicialCat.HomKernel.rel_map (fun s : Model C ↦ evaluator C s.2) α X Y h
  dagger_rel {n X Y _f _g} h :=
    DaggerSimplicialCat.HomKernel.rel_dagger (fun s : Model C ↦ evaluator C s.2) n X Y h

/-- An original identity generator agrees with the actual free identity. -/
theorem rel_id (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (X : C.Obj) :
    rel C n X X ((edge C X X).app n ((C.enriched.id X).app n PUnit.unit))
      (((free C).enriched.id X).app n PUnit.unit) := by
  intro s
  calc
    _ = (s.2.map X X).app n ((C.enriched.id X).app n PUnit.unit) :=
      edge_evaluator_app C s.2 X X n _
    _ = (s.1.enriched.id (s.2.obj X)).app n PUnit.unit :=
      congrFun (NatTrans.congr_app (s.2.map_id X) n) PUnit.unit
    _ = _ :=
      (congrFun (NatTrans.congr_app ((evaluator C s.2).map_id X) n) PUnit.unit).symm

/-- Original enriched composition agrees with concatenation of the two generators. -/
theorem rel_comp (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (X Y Z : C.Obj)
    (f : (X ⟶[SSet] Y).obj n) (g : (Y ⟶[SSet] Z).obj n) :
    rel C n X Z ((edge C X Z).app n ((C.enriched.comp X Y Z).app n (f, g)))
      (((free C).enriched.comp X Y Z).app n
        ((edge C X Y).app n f, (edge C Y Z).app n g)) := by
  intro s
  calc
    _ = (s.2.map X Z).app n ((C.enriched.comp X Y Z).app n (f, g)) :=
      edge_evaluator_app C s.2 X Z n _
    _ = (s.1.enriched.comp (s.2.obj X) (s.2.obj Y) (s.2.obj Z)).app n
        ((s.2.map X Y).app n f, (s.2.map Y Z).app n g) :=
      congrFun (NatTrans.congr_app (s.2.map_comp X Y Z) n) (f, g)
    _ = (s.1.enriched.comp (s.2.obj X) (s.2.obj Y) (s.2.obj Z)).app n
        (((evaluator C s.2).map X Y).app n ((edge C X Y).app n f),
          ((evaluator C s.2).map Y Z).app n ((edge C Y Z).app n g)) := by
      rw [edge_evaluator_app, edge_evaluator_app]
    _ = _ := (congrFun (NatTrans.congr_app ((evaluator C s.2).map_comp X Y Z) n)
      ((edge C X Y).app n f, (edge C Y Z).app n g)).symm

/-- The free dagger completion retains literally the original object type. -/
def category (C : SimplicialCat.{u, u}) : DaggerSimplicialCat.{u, u} :=
  DaggerSimplicialCat.HomQuotient.quotientCategory (relation C)

/-- The original free paths map to their actual semantic hom quotient classes. -/
def quotient (C : SimplicialCat.{u, u}) : free C ⟶ category C :=
  DaggerSimplicialCat.HomQuotient.quotientFunctor (relation C)

/-- The original already composed category maps by positive singleton generators. -/
def unit (C : SimplicialCat.{u, u}) : C ⟶ DaggerSimplicialCat.forget.obj (category C) where
  obj := id
  map X Y := edge C X Y ≫ (quotient C).map X Y
  map_id X := by
    ext n p
    cases p
    change DaggerSimplicialCat.HomQuotient.mk (relation C) n _ =
      DaggerSimplicialCat.HomQuotient.mk (relation C) n _
    exact DaggerSimplicialCat.HomQuotient.sound (relation C) n (rel_id C n X)
  map_comp X Y Z := by
    ext n p
    rcases p with ⟨f, g⟩
    change DaggerSimplicialCat.HomQuotient.mk (relation C) n _ =
      DaggerSimplicialCat.HomQuotient.mk (relation C) n _
    exact DaggerSimplicialCat.HomQuotient.sound (relation C) n (rel_comp C n X Y Z f g)

/-- Every actual input functor is one member of the defining semantic family. -/
theorem kills (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ DaggerSimplicialCat.forget.obj D) :
    DaggerSimplicialCat.HomQuotient.Kills (relation C) (evaluator C F) :=
  fun _ _ _ _ _ h ↦ h ⟨D, F⟩

/-- The original input functor extends through the actual semantic hom quotient. -/
def lift (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ DaggerSimplicialCat.forget.obj D) : category C ⟶ D :=
  DaggerSimplicialCat.HomQuotient.descend (relation C) (evaluator C F) (kills C F)

/-- Descent retains the evaluator on all free paths, not only its generators. -/
theorem quotient_lift (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ DaggerSimplicialCat.forget.obj D) :
    quotient C ≫ lift C F = evaluator C F :=
  DaggerSimplicialCat.HomQuotient.quotientFunctor_descend (relation C) _ _

/-- Restrict an actual dagger functor along the original composition-preserving unit. -/
def restrict (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (H : category C ⟶ D) : C ⟶ DaggerSimplicialCat.forget.obj D :=
  unit C ≫ DaggerSimplicialCat.forget.map H

/-- Extension followed by restriction is the entire original enriched functor. -/
theorem restrict_lift (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ DaggerSimplicialCat.forget.obj D) : restrict C (lift C F) = F := by
  apply EnrichedFunctor.ext SSet (F := restrict C (lift C F)) (G := F) (fun _ ↦ rfl)
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  ext n f
  change ((evaluator C F).map X Y).app n ((edge C X Y).app n f) = (F.map X Y).app n f
  exact edge_evaluator_app C F X Y n f

/-- Positive generators determine both directed tags and all actual quotient hom maps. -/
theorem lift_restrict (C : SimplicialCat.{u, u}) {D : DaggerSimplicialCat.{u, u}}
    (H : category C ⟶ D) : lift C (restrict C H) = H := by
  apply DaggerSimplicialCat.HomQuotient.quotientFunctor_precomp_injective (relation C)
  change quotient C ≫ lift C (restrict C H) = quotient C ≫ H
  rw [quotient_lift]
  apply (FreeDaggerSimplicialCategory.homEquiv (graph C) D).injective
  change FreeDaggerSimplicialCategory.restrict
      (FreeDaggerSimplicialCategory.lift (assignment C (restrict C H))) =
    FreeDaggerSimplicialCategory.restrict (quotient C ≫ H)
  rw [FreeDaggerSimplicialCategory.restrict_lift]
  apply DaggerSimplicialGraph.Map.ext
    (f := assignment C (restrict C H))
    (g := FreeDaggerSimplicialCategory.restrict (quotient C ≫ H)) rfl
  apply heq_of_eq
  funext X Y
  ext n p
  cases p with
  | inl f => rfl
  | inr f =>
    exact congrFun (NatTrans.congr_app
      ((FreeDaggerSimplicialCategory.restrict (quotient C ≫ H)).map_dagger Y X) n)
        (Sum.inl f)

/-- The full category-level free dagger Hom equivalence, with arbitrary object maps. -/
def homEquiv (C : SimplicialCat.{u, u}) (D : DaggerSimplicialCat.{u, u}) :
    (category C ⟶ D) ≃ (C ⟶ DaggerSimplicialCat.forget.obj D) where
  toFun := restrict C
  invFun := lift C
  left_inv := lift_restrict C
  right_inv := restrict_lift C

/-- The complete Hom equivalence is natural in every actual dagger target functor. -/
theorem homEquiv_naturality (C : SimplicialCat.{u, u})
    (D E : DaggerSimplicialCat.{u, u}) (K : D ⟶ E) (H : category C ⟶ D) :
    homEquiv C E (H ≫ K) = homEquiv C D H ≫ DaggerSimplicialCat.forget.map K := by
  change unit C ≫ DaggerSimplicialCat.forget.map (H ≫ K) = _
  rw [Functor.map_comp, ← Category.assoc]
  rfl

/-- The actual free dagger functor on already composed simplicial categories. -/
def functor : SimplicialCat.{u, u} ⥤ DaggerSimplicialCat.{u, u} :=
  Adjunction.leftAdjointOfEquiv homEquiv homEquiv_naturality

/-- The genuine ordinary-category free dagger adjunction. -/
def adjunction : functor.{u} ⊣ DaggerSimplicialCat.forget :=
  Adjunction.adjunctionOfEquivLeft homEquiv homEquiv_naturality

/-- The actual adjunction unit is the original positive-generator enriched unit. -/
theorem adjunction_unit (C : SimplicialCat.{u, u}) :
    adjunction.unit.app C = unit C := by
  change unit C ≫ DaggerSimplicialCat.forget.map (𝟙 _) = unit C
  simp

/-- The chosen functor object is the actual semantic quotient. -/
theorem functor_obj (C : SimplicialCat.{u, u}) : functor.obj C = category C := rfl

/-- The arbitrary common universe and original object type are literally retained. -/
theorem functor_obj_Obj (C : SimplicialCat.{u, u}) : (functor.obj C).Obj = C.Obj := rfl

/-- The unit fixes every original object. -/
theorem unit_obj (C : SimplicialCat.{u, u}) (X : C.Obj) : (unit C).obj X = X := rfl

/-- The unit on every actual hom simplex is the positive singleton quotient class. -/
theorem unit_map_app (C : SimplicialCat.{u, u}) (X Y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (f : (X ⟶[SSet] Y).obj n) :
    ((unit C).map X Y).app n f =
      DaggerSimplicialCat.HomQuotient.mk (relation C) n ((edge C X Y).app n f) := rfl

end DaggerModels.OrdinaryFreeDagger
