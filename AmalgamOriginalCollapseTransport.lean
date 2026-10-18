import AmalgamOriginalMonicity
import IinjBridge

/-! Transport the actual collapse's Hom weak equivalences to every original pushout apex.
The full ordinary-collapse premise is explicit; its discharge belongs to the final assembly. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory
open DaggerAmalgamPresentation DaggerAmalgamCollapse DaggerSimplicialIsoHoms
open scoped SSet.modelCategoryQuillen

universe u

set_option autoImplicit false

namespace DaggerAmalgamOriginalResults

noncomputable section

variable (C B : DaggerSimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)
variable (hOrd : ∀ a d : Objects C.toSimplicialCat B.toSimplicialCat x b,
  SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map ((ordinary C B x b).map a d))))

include hOrd in
theorem dagger_map_geometric_of_ordinary (a d : (Dagger.presentation C B x b).Obj) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map ((dagger C B x b).map a d))) := by
  have h : ∀ a d : (Dagger.presentation C B x b).Obj,
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map
        ((DaggerSimplicialCat.forget.map (dagger C B x b)).map a d))) := by
    rw [dagger_underlying]
    exact hOrd
  exact h a d

variable {P : DaggerSimplicialCat.{u, u}} (i : C ⟶ P) (j : B ⟶ P)
  (sq : IsPushout (DaggerDiscreteObjects.fromPoint C x)
    (DaggerDiscreteObjects.fromPoint B b) i j)

include hOrd in
/-- The original collapse and every original endpoint are retained. -/
theorem original_map_geometric_of_ordinary (a d : P.Obj) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map ((original C B x b i j sq).map a d))) := by
  let e := DaggerSimplicialCat.forget.mapIso (Dagger.originalIso C B x b i j sq).symm
  have : IsIso (e.hom.map a d) := mapIsIso e a d
  have : WeakEquivalence ((dagger C B x b).map (e.hom.obj a) (e.hom.obj d)) :=
    (KanQuillenReuse.weakEquivalence_iff_geometric _).2
      (dagger_map_geometric_of_ordinary C B x b hOrd (e.hom.obj a) (e.hom.obj d))
  change SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map
    (e.hom.map a d ≫ (dagger C B x b).map (e.hom.obj a) (e.hom.obj d))))
  exact (KanQuillenReuse.weakEquivalence_iff_geometric _).1 inferInstance

include hOrd j sq in
/-- Two-out-of-three applies to the SAME old-Hom map and the full splitting equation. -/
theorem original_left_geometric_of_ordinary (a d : C.Obj) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (i.map a d))) := by
  have : WeakEquivalence ((original C B x b i j sq).map (i.obj a) (i.obj d)) :=
    (KanQuillenReuse.weakEquivalence_iff_geometric _).2
      (original_map_geometric_of_ordinary C B x b hOrd i j sq (i.obj a) (i.obj d))
  have hc : WeakEquivalence ((i ≫ original C B x b i j sq).map a d) := by
    rw [original_left]
    change WeakEquivalence (𝟙 (a ⟶[SSet] d))
    infer_instance
  have : WeakEquivalence (i.map a d ≫
      (original C B x b i j sq).map (i.obj a) (i.obj d)) := hc
  exact (KanQuillenReuse.weakEquivalence_iff_geometric _).1
    (weakEquivalence_of_postcomp (i.map a d)
      ((original C B x b i j sq).map (i.obj a) (i.obj d)))

include hOrd i j sq in
/-- Compose the SAME original collapse with the original target-Hom terminal map. -/
theorem original_toUnit_geometric_of_ordinary
    (hC : ∀ a d : C.Obj, SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (toUnit (a ⟶[SSet] d)))))
    (a d : P.Obj) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit (a ⟶[SSet] d)))) := by
  let q := original C B x b i j sq
  have : WeakEquivalence (q.map a d) :=
    (KanQuillenReuse.weakEquivalence_iff_geometric _).2
      (original_map_geometric_of_ordinary C B x b hOrd i j sq a d)
  have : WeakEquivalence (toUnit (q.obj a ⟶[SSet] q.obj d)) :=
    (KanQuillenReuse.weakEquivalence_iff_geometric _).2 (hC (q.obj a) (q.obj d))
  have hc : WeakEquivalence (q.map a d ≫ toUnit (q.obj a ⟶[SSet] q.obj d)) := inferInstance
  have he : q.map a d ≫ toUnit (q.obj a ⟶[SSet] q.obj d) = toUnit (a ⟶[SSet] d) :=
    isTerminalTensorUnit.hom_ext _ _
  rw [he] at hc
  exact (KanQuillenReuse.weakEquivalence_iff_geometric _).1 hc

end
end DaggerAmalgamOriginalResults
