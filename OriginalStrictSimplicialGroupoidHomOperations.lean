import OriginalSimplicialGroupoidCompletionUniversal

/-!
# Pointwise operations on the original strict simplicial groupoid Hom

Keep the original enriched Hom, identities and composition. Invertibility in the
original degree categories supplies pointwise inverse. Every original simplicial
operator preserves these operations. These are the actual operations used to
construct horn fillers on the original mapping simplicial sets.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialGroupoidCompletionUniversal

universe u

namespace DaggerOriginalStrictSimplicialGroupoidHomOperations

noncomputable section

/-- The same original mapping simplices in the indicated dimension. -/
abbrev PointHom (C : SimplicialCat.{u, u}) (n : ℕ) (x y : C.Obj) :=
  (C.enriched.Hom x y).obj (op ⦋n⦌)

/-- The identity is the original enriched identity evaluated in its original degree. -/
def pointId (C : SimplicialCat.{u, u}) (n : ℕ) (x : C.Obj) : PointHom C n x x :=
  (C.enriched.id x).app (op ⦋n⦌) PUnit.unit

/-- Composition is the original enriched composition evaluated in its original degree. -/
def pointComp (C : SimplicialCat.{u, u}) (n : ℕ) {x y z : C.Obj}
    (f : PointHom C n x y) (g : PointHom C n y z) : PointHom C n x z :=
  (C.enriched.comp x y z).app (op ⦋n⦌) (f, g)

/-- The inverse is native inverse in the unchanged original ordinary degree category. -/
def pointInverse (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    {x y : C.Obj} (f : PointHom C n x y) : PointHom C n y x :=
  @inv (degreeObjects C (op ⦋n⦌)) (degreeCategory C (op ⦋n⦌)) x y f (hC _ x y f)

/-- Pointwise composition retains original associativity. -/
theorem pointComp_assoc (C : SimplicialCat.{u, u}) (n : ℕ) {w x y z : C.Obj}
    (f : PointHom C n w x) (g : PointHom C n x y) (h : PointHom C n y z) :
    pointComp C n (pointComp C n f g) h = pointComp C n f (pointComp C n g h) :=
  @Category.assoc (degreeObjects C (op ⦋n⦌)) (degreeCategory C (op ⦋n⦌)) w x y z f g h

/-- Pointwise left identity is the original degree identity law. -/
theorem pointId_comp (C : SimplicialCat.{u, u}) (n : ℕ) {x y : C.Obj}
    (f : PointHom C n x y) : pointComp C n (pointId C n x) f = f :=
  @Category.id_comp (degreeObjects C (op ⦋n⦌)) (degreeCategory C (op ⦋n⦌)) x y f

/-- Pointwise right identity is the original degree identity law. -/
theorem pointComp_id (C : SimplicialCat.{u, u}) (n : ℕ) {x y : C.Obj}
    (f : PointHom C n x y) : pointComp C n f (pointId C n y) = f :=
  @Category.comp_id (degreeObjects C (op ⦋n⦌)) (degreeCategory C (op ⦋n⦌)) x y f

/-- Pointwise inverse cancels the original arrow on the left. -/
theorem pointInverse_comp (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    {x y : C.Obj} (f : PointHom C n x y) :
    pointComp C n (pointInverse C hC n f) f = pointId C n y := by
  exact @IsIso.inv_hom_id (degreeObjects C (op ⦋n⦌)) (degreeCategory C (op ⦋n⦌))
    x y f (hC _ x y f)

/-- Pointwise inverse cancels the original arrow on the right. -/
theorem pointComp_inverse (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) (n : ℕ)
    {x y : C.Obj} (f : PointHom C n x y) :
    pointComp C n f (pointInverse C hC n f) = pointId C n x := by
  exact @IsIso.hom_inv_id (degreeObjects C (op ⦋n⦌)) (degreeCategory C (op ⦋n⦌))
    x y f (hC _ x y f)

/-- Every original simplicial operator preserves the original identity. -/
theorem pointId_map (C : SimplicialCat.{u, u}) {n m : ℕ} (i : op ⦋n⦌ ⟶ op ⦋m⦌)
    (x : C.Obj) : (C.enriched.Hom x x).map i (pointId C n x) = pointId C m x :=
  (congrFun ((C.enriched.id x).naturality i) PUnit.unit).symm

/-- Every original simplicial operator preserves the original composition. -/
theorem pointComp_map (C : SimplicialCat.{u, u}) {n m : ℕ} (i : op ⦋n⦌ ⟶ op ⦋m⦌)
    {x y z : C.Obj} (f : PointHom C n x y) (g : PointHom C n y z) :
    (C.enriched.Hom x z).map i (pointComp C n f g) =
      pointComp C m ((C.enriched.Hom x y).map i f) ((C.enriched.Hom y z).map i g) :=
  (congrFun ((C.enriched.comp x y z).naturality i) (f, g)).symm

/-- Every original simplicial operator preserves the native original degree inverse. -/
theorem pointInverse_map (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    {n m : ℕ} (i : op ⦋n⦌ ⟶ op ⦋m⦌) {x y : C.Obj} (f : PointHom C n x y) :
    (C.enriched.Hom y x).map i (pointInverse C hC n f) =
      pointInverse C hC m ((C.enriched.Hom x y).map i f) := by
  have : IsIso (C := degreeObjects C (op ⦋n⦌)) f := hC _ x y f
  exact (degreeMap C i).map_inv f

/-- Each original face preserves the original composition. -/
theorem pointComp_face (C : SimplicialCat.{u, u}) (n : ℕ) (i : Fin (n + 2))
    {x y z : C.Obj} (f : PointHom C (n + 1) x y) (g : PointHom C (n + 1) y z) :
    (C.enriched.Hom x z).δ i (pointComp C (n + 1) f g) =
      pointComp C n ((C.enriched.Hom x y).δ i f) ((C.enriched.Hom y z).δ i g) :=
  pointComp_map C (SimplexCategory.δ i).op f g

/-- Each original face preserves the original degree inverse. -/
theorem pointInverse_face (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (n : ℕ) (i : Fin (n + 2)) {x y : C.Obj} (f : PointHom C (n + 1) x y) :
    (C.enriched.Hom y x).δ i (pointInverse C hC (n + 1) f) =
      pointInverse C hC n ((C.enriched.Hom x y).δ i f) :=
  pointInverse_map C hC (SimplexCategory.δ i).op f

end

end DaggerOriginalStrictSimplicialGroupoidHomOperations
