import OriginalFixedObjectProducts

/-!
# Products of the original fixed-object dagger categories

The underlying product is the proved original fixed-O product. Pair the two
original dagger maps, with their full involution, identity and composition
laws. The actual projections and pairing preserve that dagger. Restricting to
strict groupoids retains the whole original universal property.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectProducts
universe u

namespace DaggerOriginalFixedObjectDaggerProducts

noncomputable section

/-- Pair the exact original daggers on the already proved product enrichment. -/
def productDagger {O : Type u} (C D : FixedDaggerCategory O) :
    @DaggerSimplicialStructure O (product C.underlying D.underlying).enriched := by
  letI := (product C.underlying D.underlying).enriched
  refine
    { dagger := fun x y ↦ C.dagger.dagger x y ⊗ₘ D.dagger.dagger x y
      dagger_involutive := ?_
      dagger_id := ?_
      dagger_comp := ?_ }
  · intro x y
    apply NatTrans.ext
    funext n f
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (C.dagger.dagger_involutive x y) n) f.1
    · exact congrFun (NatTrans.congr_app (D.dagger.dagger_involutive x y) n) f.2
  · intro x
    apply NatTrans.ext
    funext n p
    cases p
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (C.dagger.dagger_id x) n) PUnit.unit
    · exact congrFun (NatTrans.congr_app (D.dagger.dagger_id x) n) PUnit.unit
  · intro x y z
    apply NatTrans.ext
    funext n p
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (C.dagger.dagger_comp x y z) n) (p.1.1, p.2.1)
    · exact congrFun (NatTrans.congr_app (D.dagger.dagger_comp x y z) n) (p.1.2, p.2.2)

/-- The actual dagger product has precisely the original object set O. -/
def daggerProduct {O : Type u} (C D : FixedDaggerCategory O) : FixedDaggerCategory O :=
  ⟨product C.underlying D.underlying, productDagger C D⟩

/-- The actual first projection preserves the exact original dagger. -/
def daggerFst {O : Type u} (C D : FixedDaggerCategory O) : daggerProduct C D ⟶ C where
  underlying := fst C.underlying D.underlying
  map_dagger _ _ := by apply NatTrans.ext; funext n f; rfl

/-- The actual second projection preserves the exact original dagger. -/
def daggerSnd {O : Type u} (C D : FixedDaggerCategory O) : daggerProduct C D ⟶ D where
  underlying := snd C.underlying D.underlying
  map_dagger _ _ := by apply NatTrans.ext; funext n f; rfl

/-- Pair the full original dagger functors on the same fixed object set. -/
def daggerLift {O : Type u} {A C D : FixedDaggerCategory O} (F : A ⟶ C) (G : A ⟶ D) :
    A ⟶ daggerProduct C D where
  underlying := lift F.underlying G.underlying
  map_dagger x y := by
    apply NatTrans.ext
    funext n f
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (F.map_dagger x y) n) f
    · exact congrFun (NatTrans.congr_app (G.map_dagger x y) n) f

/-- First projection recovers the whole original dagger functor. -/
theorem daggerLift_fst {O : Type u} {A C D : FixedDaggerCategory O} (F : A ⟶ C) (G : A ⟶ D) :
    daggerLift F G ≫ daggerFst C D = F :=
  fixedDaggerHom_ext (lift_fst F.underlying G.underlying)

/-- Second projection recovers the whole original dagger functor. -/
theorem daggerLift_snd {O : Type u} {A C D : FixedDaggerCategory O} (F : A ⟶ C) (G : A ⟶ D) :
    daggerLift F G ≫ daggerSnd C D = G :=
  fixedDaggerHom_ext (lift_snd F.underlying G.underlying)

/-- The two projections determine every original dagger functor into the product. -/
theorem daggerLift_eta {O : Type u} {A C D : FixedDaggerCategory O}
    (F : A ⟶ daggerProduct C D) :
    daggerLift (F ≫ daggerFst C D) (F ≫ daggerSnd C D) = F :=
  fixedDaggerHom_ext (lift_eta F.underlying)

/-- The full original dagger diagonal, retaining the same identity object function. -/
def daggerDiagonal {O : Type u} (C : FixedDaggerCategory O) : C ⟶ daggerProduct C C :=
  daggerLift (𝟙 C) (𝟙 C)

/-- The same original product is strict whenever both original dagger factors are strict. -/
def strictDaggerProduct {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    FixedStrictDaggerGroupoids O :=
  ⟨daggerProduct C.obj D.obj,
    product_strict ⟨C.obj.underlying, C.property⟩ ⟨D.obj.underlying, D.property⟩⟩

/-- First projection is an actual arrow of the original strict dagger category. -/
def strictDaggerFst {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    strictDaggerProduct C D ⟶ C := ObjectProperty.homMk (daggerFst C.obj D.obj)

/-- Second projection is an actual arrow of the original strict dagger category. -/
def strictDaggerSnd {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    strictDaggerProduct C D ⟶ D := ObjectProperty.homMk (daggerSnd C.obj D.obj)

/-- Pair the full original strict dagger functors. -/
def strictDaggerLift {O : Type u} {A C D : FixedStrictDaggerGroupoids O}
    (F : A ⟶ C) (G : A ⟶ D) : A ⟶ strictDaggerProduct C D :=
  ObjectProperty.homMk (daggerLift F.hom G.hom)

/-- Pairing recovers the first original strict dagger functor. -/
theorem strictDaggerLift_fst {O : Type u} {A C D : FixedStrictDaggerGroupoids O}
    (F : A ⟶ C) (G : A ⟶ D) : strictDaggerLift F G ≫ strictDaggerFst C D = F :=
  ObjectProperty.hom_ext _ (daggerLift_fst F.hom G.hom)

/-- Pairing recovers the second original strict dagger functor. -/
theorem strictDaggerLift_snd {O : Type u} {A C D : FixedStrictDaggerGroupoids O}
    (F : A ⟶ C) (G : A ⟶ D) : strictDaggerLift F G ≫ strictDaggerSnd C D = G :=
  ObjectProperty.hom_ext _ (daggerLift_snd F.hom G.hom)

/-- Both projections determine the entire original strict dagger functor. -/
theorem strictDaggerLift_eta {O : Type u} {A C D : FixedStrictDaggerGroupoids O}
    (F : A ⟶ strictDaggerProduct C D) :
    strictDaggerLift (F ≫ strictDaggerFst C D) (F ≫ strictDaggerSnd C D) = F :=
  ObjectProperty.hom_ext _ (daggerLift_eta F.hom)

/-- The actual categorical diagonal in the unchanged fixed-object strict dagger category. -/
def strictDaggerDiagonal {O : Type u} (C : FixedStrictDaggerGroupoids O) :
    C ⟶ strictDaggerProduct C C := strictDaggerLift (𝟙 C) (𝟙 C)

end

end DaggerOriginalFixedObjectDaggerProducts
