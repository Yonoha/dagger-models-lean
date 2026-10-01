import DaggerModels.SimplicialCat
import DaggerModels.SimplicialEnrichment
import Mathlib.CategoryTheory.Quotient

/-! Ordinary hom quotient: no dagger is supplied or imposed.
The original objects and ordinary simplex operators are retained. -/

open CategoryTheory MonoidalCategory

universe o v

namespace DaggerModels.SimplicialCat.HomQuotient

variable (C : SimplicialCat.{o, v})

/-- The original mapping-space simplices in the specified degree. -/
abbrev RawHom (n : SimplexCategoryᵒᵖ) (x y : C.Obj) := (x ⟶[SSet.{v}] y).obj n

/-- Generating hom relations preserved by ordinary simplex maps. -/
structure StableHomRel where
  rel : ∀ (n : SimplexCategoryᵒᵖ) (x y : C.Obj), RawHom C n x y → RawHom C n x y → Prop
  map_rel : ∀ {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) {x y : C.Obj}
    {f g : RawHom C n x y}, rel n x y f g →
      rel m x y ((x ⟶[SSet.{v}] y).map α f) ((x ⟶[SSet.{v}] y).map α g)


variable {C} (R : StableHomRel C)

/-- Interpret the relation in the actual category of one simplicial degree. -/
def degreeRel (n : SimplexCategoryᵒᵖ) : HomRel (SimplicialEnrichment.At C.Obj n) :=
  fun {x y} f g ↦ R.rel n x y f g

private theorem map_compClosure {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    {x y : SimplicialEnrichment.At C.Obj n} {f g : x ⟶ y}
    (h : HomRel.CompClosure (degreeRel R n) f g) :
    HomRel.CompClosure (degreeRel R m)
      ((SimplicialEnrichment.map C.Obj α).map f)
      ((SimplicialEnrichment.map C.Obj α).map g) := by
  rcases h with ⟨a, b, p, f, g, q, h⟩
  simpa only [CategoryTheory.Functor.map_comp] using
    HomRel.CompClosure.intro
      ((SimplicialEnrichment.map C.Obj α).obj a)
      ((SimplicialEnrichment.map C.Obj α).obj b)
      ((SimplicialEnrichment.map C.Obj α).map p)
      ((SimplicialEnrichment.map C.Obj α).map f)
      ((SimplicialEnrichment.map C.Obj α).map g)
      ((SimplicialEnrichment.map C.Obj α).map q) (R.map_rel α h)

/-- Actual quotient homs, retaining the original two object labels. -/
abbrev HomObj (n : SimplexCategoryᵒᵖ) (x y : C.Obj) :=
  Quotient.Hom (degreeRel R n) ⟨x⟩ ⟨y⟩

/-- The quotient of an original mapping-space simplex. -/
def mk (n : SimplexCategoryᵒᵖ) {x y : C.Obj} (f : RawHom C n x y) : HomObj R n x y :=
  Quot.mk _ f

/-- The same ordinary simplex operator on the quotient hom spaces. -/
def map {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) {x y : C.Obj} :
    HomObj R n x y → HomObj R m x y :=
  Quot.map (fun f ↦ (SimplicialEnrichment.map C.Obj α).map f)
    (fun _ _ h ↦ map_compClosure R α h)

@[simp] theorem map_mk {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) {x y : C.Obj}
    (f : RawHom C n x y) : map R α (mk R n f) = mk R m ((x ⟶[SSet.{v}] y).map α f) := rfl

/-- The mapping simplicial set of quotient homs. -/
def hom (x y : C.Obj) : SSet.{v} where
  obj n := HomObj R n x y
  map α := map R α
  map_id n := by
    funext f
    refine Quot.inductionOn f (fun f ↦ ?_)
    change mk R n ((x ⟶[SSet.{v}] y).map (𝟙 n) f) = mk R n f
    rw [FunctorToTypes.map_id_apply]
  map_comp α β := by
    funext f
    refine Quot.inductionOn f (fun f ↦ ?_)
    change mk R _ ((x ⟶[SSet.{v}] y).map (α ≫ β) f) =
      mk R _ ((x ⟶[SSet.{v}] y).map β ((x ⟶[SSet.{v}] y).map α f))
    rw [FunctorToTypes.map_comp_apply]

/-- The enriched identity, as the class of the original enriched identity. -/
def id (x : C.Obj) : 𝟙_ SSet.{v} ⟶ hom R x x where
  app n _ := mk R n ((eId SSet x).app n PUnit.unit)
  naturality {n m} α := by
    funext e
    change mk R m ((eId SSet x).app m PUnit.unit) =
      mk R m ((x ⟶[SSet.{v}] x).map α ((eId SSet x).app n PUnit.unit))
    exact congrArg (mk R m) (congrFun ((eId SSet x).naturality α) PUnit.unit)

/-- Composition is Mathlib's actual composition in each hom quotient. -/
def comp (x y z : C.Obj) : hom R x y ⊗ hom R y z ⟶ hom R x z where
  app n p := Quotient.comp (degreeRel R n) p.1 p.2
  naturality {n m} α := by
    funext p
    rcases p with ⟨f, g⟩
    refine Quot.inductionOn f (fun f ↦ ?_)
    refine Quot.inductionOn g (fun g ↦ ?_)
    change mk R m ((eComp SSet x y z).app m
      ((x ⟶[SSet.{v}] y).map α f, (y ⟶[SSet.{v}] z).map α g)) =
        mk R m ((x ⟶[SSet.{v}] z).map α ((eComp SSet x y z).app n (f, g)))
    exact congrArg (mk R m) (congrFun ((eComp SSet x y z).naturality α) (f, g))

/-- The actual quotient enrichment on exactly the original object type. -/
def enrichedCategory : EnrichedCategory SSet.{v} C.Obj where
  Hom := hom R
  id := id R
  comp := comp R
  id_comp x y := by
    ext n f
    refine Quot.inductionOn f (fun f ↦ ?_)
    exact congrArg (mk R n) (congrFun (NatTrans.congr_app (e_id_comp SSet x y) n) f)
  comp_id x y := by
    ext n f
    refine Quot.inductionOn f (fun f ↦ ?_)
    exact congrArg (mk R n) (congrFun (NatTrans.congr_app (e_comp_id SSet x y) n) f)
  assoc w x y z := by
    ext n p
    rcases p with ⟨f, g, h⟩
    refine Quot.inductionOn f (fun f ↦ ?_)
    refine Quot.inductionOn g (fun g ↦ ?_)
    refine Quot.inductionOn h (fun h ↦ ?_)
    exact congrArg (mk R n)
      (congrFun (NatTrans.congr_app (e_assoc SSet w x y z) n) (f, g, h))

/-- The bundled quotient retains literally the original object type. -/
def quotientCategory : SimplicialCat.{o, v} :=
  ⟨C.Obj, enrichedCategory R⟩

/-- Send every original hom simplex to its quotient class. -/
def quotientFunctor : C ⟶ quotientCategory R :=
    { obj := fun x ↦ x
      map := fun x y ↦
        { app := fun n f ↦ mk R n f
          naturality := fun {_ _} _ ↦ rfl }
      map_id := fun _ ↦ by ext n e; cases e; rfl
      map_comp := fun _ _ _ ↦ by ext n p; rfl }
@[simp] theorem quotientFunctor_obj (x : C.Obj) : (quotientFunctor R).obj x = x := rfl

@[simp] theorem quotientFunctor_map_app (n : SimplexCategoryᵒᵖ) {x y : C.Obj}
    (f : RawHom C n x y) : ((quotientFunctor R).map x y).app n f = mk R n f := rfl

/-- Every generating relation becomes an actual equality of hom simplices. -/
theorem sound (n : SimplexCategoryᵒᵖ) {x y : C.Obj} {f g : RawHom C n x y}
    (h : R.rel n x y f g) : mk R n f = mk R n g :=
  Quot.sound (HomRel.CompClosure.of h)

/-- An actual ordinary enriched functor kills every specified generating relation. -/
def Kills {D : SimplicialCat.{o, v}} (F : C ⟶ D) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ) (x y : C.Obj) (f g : RawHom C n x y),
    R.rel n x y f g → (F.map x y).app n f = (F.map x y).app n g

/-- Descend a relation-killing functor through the actual hom quotients. -/
def descend {D : SimplicialCat.{o, v}} (F : C ⟶ D) (hF : Kills R F) :
    quotientCategory R ⟶ D :=
    { obj := F.obj
      map := fun x y ↦
        { app := fun n f ↦
            (CategoryTheory.Quotient.lift (degreeRel R n)
              (SimplicialEnrichment.functor F n)
              (fun x y f g h ↦ hF n x y f g h)).map f
          naturality := fun {n m} α ↦ by
            funext f
            refine Quot.inductionOn f (fun f ↦ ?_)
            exact congrFun ((F.map x y).naturality α) f }
      map_id := fun x ↦ by
        ext n e
        cases e
        exact congrFun (NatTrans.congr_app (F.map_id x) n) PUnit.unit
      map_comp := fun x y z ↦ by
        ext n p
        rcases p with ⟨f, g⟩
        refine Quot.inductionOn f (fun f ↦ ?_)
        refine Quot.inductionOn g (fun g ↦ ?_)
        exact congrFun (NatTrans.congr_app (F.map_comp x y z) n) (f, g) }
@[simp] theorem descend_obj {D : SimplicialCat.{o, v}} (F : C ⟶ D) (hF : Kills R F)
    (x : C.Obj) : (descend R F hF).obj x = F.obj x := rfl

@[simp] theorem descend_map_mk {D : SimplicialCat.{o, v}} (F : C ⟶ D)
    (hF : Kills R F) (n : SimplexCategoryᵒᵖ) {x y : C.Obj} (f : RawHom C n x y) :
    ((descend R F hF).map x y).app n (mk R n f) = (F.map x y).app n f := rfl

/-- Descending a functor retains all its original object and hom maps. -/
theorem quotientFunctor_descend {D : SimplicialCat.{o, v}} (F : C ⟶ D)
    (hF : Kills R F) : quotientFunctor R ≫ descend R F hF = F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- Every hom map of the quotient functor is an epimorphism of simplicial sets. -/
instance quotientFunctor_map_epi (x y : C.Obj) : Epi ((quotientFunctor R).map x y) where
  left_cancellation f g h := by
    ext n q
    refine Quot.inductionOn q (fun q ↦ ?_)
    exact congrFun (NatTrans.congr_app h n) q

private theorem comp_eqToHom_of_heq {A B B' : SSet.{v}} {f : A ⟶ B} {g : A ⟶ B'}
    (h : B = B') (hh : HEq f g) : f ≫ eqToHom h = g := by
  subst h
  simpa using eq_of_heq hh

/-- A quotient functor is determined by its precomposition with the original category. -/
theorem quotientFunctor_precomp_injective {D : SimplicialCat.{o, v}} :
    Function.Injective (fun F : quotientCategory R ⟶ D ↦ quotientFunctor R ≫ F) := by
  intro F G h
  apply EnrichedFunctor.ext SSet (F := F) (G := G)
    (fun x ↦ congrArg (fun F : C ⟶ D ↦ F.obj x) h)
  intro x y
  apply (cancel_epi ((quotientFunctor R).map x y)).1
  rw [← Category.assoc]
  apply comp_eqToHom_of_heq
  exact congr_arg_heq (fun F : C ⟶ D ↦ F.map x y) h

/-- The descended functor is the unique actual ordinary enriched factorization. -/
theorem descend_unique {D : SimplicialCat.{o, v}} (F : C ⟶ D) (hF : Kills R F)
    (L : quotientCategory R ⟶ D) (hL : quotientFunctor R ≫ L = F) :
    L = descend R F hF :=
  quotientFunctor_precomp_injective R (hL.trans (quotientFunctor_descend R F hF).symm)

/-- Precomposing any actual quotient functor kills every generating relation. -/
theorem quotientFunctor_comp_kills {D : SimplicialCat.{o, v}}
    (F : quotientCategory R ⟶ D) : Kills R (quotientFunctor R ≫ F) := by
  intro n x y f g h
  exact congrArg ((F.map x y).app n) (sound R n h)

/-- The full universal property, allowing arbitrary object maps in the target. -/
def homEquiv (D : SimplicialCat.{o, v}) :
    (quotientCategory R ⟶ D) ≃ {F : C ⟶ D // Kills R F} where
  toFun F := ⟨quotientFunctor R ≫ F, quotientFunctor_comp_kills R F⟩
  invFun F := descend R F.val F.property
  left_inv F := (descend_unique R _ (quotientFunctor_comp_kills R F) F rfl).symm
  right_inv F := Subtype.ext (quotientFunctor_descend R F.val F.property)

end DaggerModels.SimplicialCat.HomQuotient
