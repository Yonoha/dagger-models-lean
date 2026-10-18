import OriginalFixedObjectGroupoidHomPathFactorization
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Products on the original fixed object set

Take the native product of the two original Hom simplicial sets, retaining
precisely O. Every degree operation is the original operation in each factor.
The projections and pairing are full original enriched functors, with their
entire universal property. Strictness uses the two actual original inverses.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalSimplicialDegreeCategory
universe u

namespace DaggerOriginalFixedObjectProducts

noncomputable section

/-- Identity on the paired original Hom, in every simplicial degree. -/
def productId {O : Type u} (C D : FixedSimplicialCategory O) (x : O) :
    𝟙_ SSet.{u} ⟶ C.enriched.Hom x x ⊗ D.enriched.Hom x x where
  app n _ := ((C.enriched.id x).app n PUnit.unit, (D.enriched.id x).app n PUnit.unit)
  naturality _ _ i := by
    funext p
    apply Prod.ext
    · exact congrFun ((C.enriched.id x).naturality i) PUnit.unit
    · exact congrFun ((D.enriched.id x).naturality i) PUnit.unit

/-- Compose the two original Hom components, with unchanged endpoints. -/
def productComp {O : Type u} (C D : FixedSimplicialCategory O) (x y z : O) :
    (C.enriched.Hom x y ⊗ D.enriched.Hom x y) ⊗
        (C.enriched.Hom y z ⊗ D.enriched.Hom y z) ⟶
      C.enriched.Hom x z ⊗ D.enriched.Hom x z where
  app n p := ((C.enriched.comp x y z).app n (p.1.1, p.2.1),
    (D.enriched.comp x y z).app n (p.1.2, p.2.2))
  naturality _ _ i := by
    funext p
    apply Prod.ext
    · exact congrFun ((C.enriched.comp x y z).naturality i) (p.1.1, p.2.1)
    · exact congrFun ((D.enriched.comp x y z).naturality i) (p.1.2, p.2.2)

/-- The actual product enrichment retains exactly the original object set O. -/
def product {O : Type u} (C D : FixedSimplicialCategory O) : FixedSimplicialCategory O where
  enriched :=
    { Hom x y := C.enriched.Hom x y ⊗ D.enriched.Hom x y
      id := productId C D
      comp := productComp C D
      id_comp x y := by
        apply NatTrans.ext
        funext n f
        apply Prod.ext
        · exact congrFun (NatTrans.congr_app (C.enriched.id_comp x y) n) f.1
        · exact congrFun (NatTrans.congr_app (D.enriched.id_comp x y) n) f.2
      comp_id x y := by
        apply NatTrans.ext
        funext n f
        apply Prod.ext
        · exact congrFun (NatTrans.congr_app (C.enriched.comp_id x y) n) f.1
        · exact congrFun (NatTrans.congr_app (D.enriched.comp_id x y) n) f.2
      assoc w x y z := by
        apply NatTrans.ext
        funext n f
        apply Prod.ext
        · exact congrFun (NatTrans.congr_app (C.enriched.assoc w x y z) n)
            (f.1.1, (f.2.1.1, f.2.2.1))
        · exact congrFun (NatTrans.congr_app (D.enriched.assoc w x y z) n)
            (f.1.2, (f.2.1.2, f.2.2.2)) }

/-- The first projection is the native first projection on every original Hom. -/
def fst {O : Type u} (C D : FixedSimplicialCategory O) : product C D ⟶ C where
  map x y := CartesianMonoidalCategory.fst _ _
  map_id _ := by apply NatTrans.ext; funext n p; rfl
  map_comp _ _ _ := by apply NatTrans.ext; funext n p; rfl

/-- The second projection is the native second projection on every original Hom. -/
def snd {O : Type u} (C D : FixedSimplicialCategory O) : product C D ⟶ D where
  map x y := CartesianMonoidalCategory.snd _ _
  map_id _ := by apply NatTrans.ext; funext n p; rfl
  map_comp _ _ _ := by apply NatTrans.ext; funext n p; rfl

/-- Pair two full original fixed-object functors, retaining all enriched laws. -/
def lift {O : Type u} {A C D : FixedSimplicialCategory O} (F : A ⟶ C) (G : A ⟶ D) :
    A ⟶ product C D where
  map x y := CartesianMonoidalCategory.lift (F.map x y) (G.map x y)
  map_id x := by
    apply NatTrans.ext
    funext n p
    cases p
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (F.map_id x) n) PUnit.unit
    · exact congrFun (NatTrans.congr_app (G.map_id x) n) PUnit.unit
  map_comp x y z := by
    apply NatTrans.ext
    funext n p
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app (F.map_comp x y z) n) p
    · exact congrFun (NatTrans.congr_app (G.map_comp x y z) n) p

/-- The first projection recovers the entire first original functor. -/
theorem lift_fst {O : Type u} {A C D : FixedSimplicialCategory O} (F : A ⟶ C) (G : A ⟶ D) :
    lift F G ≫ fst C D = F := by
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  rfl

/-- The second projection recovers the entire second original functor. -/
theorem lift_snd {O : Type u} {A C D : FixedSimplicialCategory O} (F : A ⟶ C) (G : A ⟶ D) :
    lift F G ≫ snd C D = G := by
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  rfl

/-- Both projections together determine the entire original functor into the product. -/
theorem lift_eta {O : Type u} {A C D : FixedSimplicialCategory O} (F : A ⟶ product C D) :
    lift (F ≫ fst C D) (F ≫ snd C D) = F := by
  apply fixedHom_ext
  intro x y
  apply NatTrans.ext
  funext n f
  rfl

/-- The actual categorical diagonal has the unchanged native diagonal on every original Hom. -/
def diagonal {O : Type u} (C : FixedSimplicialCategory O) : C ⟶ product C C := lift (𝟙 C) (𝟙 C)

/-- The degreewise product is a strict groupoid by the two original inverse equations. -/
theorem product_strict {O : Type u} (C D : FixedStrictGroupoids O) :
    IsStrictFixed (product C.obj D.obj) := by
  intro n x y f
  let g := (@inv (degreeObjects (original O C.obj) n) (degreeCategory (original O C.obj) n)
      x y f.1 (C.property n x y f.1),
    @inv (degreeObjects (original O D.obj) n) (degreeCategory (original O D.obj) n)
      x y f.2 (D.property n x y f.2))
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply Prod.ext
    · exact @IsIso.hom_inv_id (degreeObjects (original O C.obj) n)
        (degreeCategory (original O C.obj) n) x y f.1 (C.property n x y f.1)
    · exact @IsIso.hom_inv_id (degreeObjects (original O D.obj) n)
        (degreeCategory (original O D.obj) n) x y f.2 (D.property n x y f.2)
  · apply Prod.ext
    · exact @IsIso.inv_hom_id (degreeObjects (original O C.obj) n)
        (degreeCategory (original O C.obj) n) x y f.1 (C.property n x y f.1)
    · exact @IsIso.inv_hom_id (degreeObjects (original O D.obj) n)
        (degreeCategory (original O D.obj) n) x y f.2 (D.property n x y f.2)

/-- The full original product remains in the exact fixed-object strict groupoid category. -/
def strictProduct {O : Type u} (C D : FixedStrictGroupoids O) : FixedStrictGroupoids O :=
  ⟨product C.obj D.obj, product_strict C D⟩

/-- First projection in the original strict category. -/
def strictFst {O : Type u} (C D : FixedStrictGroupoids O) : strictProduct C D ⟶ C :=
  ObjectProperty.homMk (fst C.obj D.obj)

/-- Second projection in the original strict category. -/
def strictSnd {O : Type u} (C D : FixedStrictGroupoids O) : strictProduct C D ⟶ D :=
  ObjectProperty.homMk (snd C.obj D.obj)

/-- The same full pairing is an arrow of the original strict category. -/
def strictLift {O : Type u} {A C D : FixedStrictGroupoids O} (F : A ⟶ C) (G : A ⟶ D) :
    A ⟶ strictProduct C D := ObjectProperty.homMk (lift F.hom G.hom)

/-- Pairing recovers the first original strict functor. -/
theorem strictLift_fst {O : Type u} {A C D : FixedStrictGroupoids O} (F : A ⟶ C) (G : A ⟶ D) :
    strictLift F G ≫ strictFst C D = F := ObjectProperty.hom_ext _ (lift_fst F.hom G.hom)

/-- Pairing recovers the second original strict functor. -/
theorem strictLift_snd {O : Type u} {A C D : FixedStrictGroupoids O} (F : A ⟶ C) (G : A ⟶ D) :
    strictLift F G ≫ strictSnd C D = G := ObjectProperty.hom_ext _ (lift_snd F.hom G.hom)

/-- Both projections determine the original strict groupoid functor. -/
theorem strictLift_eta {O : Type u} {A C D : FixedStrictGroupoids O}
    (F : A ⟶ strictProduct C D) : strictLift (F ≫ strictFst C D) (F ≫ strictSnd C D) = F :=
  ObjectProperty.hom_ext _ (lift_eta F.hom)

/-- The unchanged diagonal in the actual fixed-object strict groupoid category. -/
def strictDiagonal {O : Type u} (C : FixedStrictGroupoids O) : C ⟶ strictProduct C C :=
  strictLift (𝟙 C) (𝟙 C)

end

end DaggerOriginalFixedObjectProducts
