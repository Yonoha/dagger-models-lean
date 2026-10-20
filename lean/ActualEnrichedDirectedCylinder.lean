import OriginalOrdinaryTranslationRecovered
import SSetGluing

/-! Directed cylinder comparisons using a weak Hom projection. -/

set_option autoImplicit false
open CategoryTheory EnrichedCategory Opposite Simplicial HomotopicalAlgebra
open DaggerOrdinaryPiZeroCategory DaggerOrdinaryTranslation DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe o p q u

namespace DaggerActualEnrichedDirectedCylinder

noncomputable section

variable {A : DaggerModels.SimplicialCat.{o, u}}
  {B : DaggerModels.SimplicialCat.{p, u}}
  {D : DaggerModels.SimplicialCat.{q, u}}

/-- The image of an identity vertex is invertible in the original component category. -/
theorem mapped_id_class_isIso (F : EnrichedFunctor SSet.{u} A.Obj B.Obj) (x : A.Obj) :
    IsIso (classOfVertex B ((F.map x x).app (op ⦋0⦌) (idVertex A x))) := by
  change IsIso ((hFunctor F).map (classOfVertex A (idVertex A x)))
  rw [classOfVertex_id]
  infer_instance

/-- Weak projected Hom maps detect weak translation without invertibility in the source. -/
theorem translation_GW_of_projection
    (P : EnrichedFunctor SSet.{u} A.Obj B.Obj) {x' x y y' : A.Obj}
    (a : (x' ⟶[SSet.{u}] x).obj (op ⦋0⦌))
    (b : (y ⟶[SSet.{u}] y').obj (op ⦋0⦌))
    [IsIso (classOfVertex B ((P.map x' x).app (op ⦋0⦌) a))]
    [IsIso (classOfVertex B ((P.map y y').app (op ⦋0⦌) b))]
    (h₀ : GW (P.map x y)) (h₁ : GW (P.map x' y')) : GW (translation A a b) := by
  have : WeakEquivalence (P.map x y) := (weakEquivalence_iff_GW _).2 h₀
  have : WeakEquivalence (P.map x' y') := (weakEquivalence_iff_GW _).2 h₁
  have : WeakEquivalence
      (translation B ((P.map x' x).app (op ⦋0⦌) a)
        ((P.map y y').app (op ⦋0⦌) b)) := translation_weakEquivalence B _ _
  have : WeakEquivalence (translation A a b ≫ P.map x' y') := by
    rw [translation_naturality P a b]
    infer_instance
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_postcomp (translation A a b) (P.map x' y'))

/-- A weak source translation and invertible target vertices compare the actual Hom maps. -/
theorem map_GW_iff_translation
    (F : EnrichedFunctor SSet.{u} A.Obj D.Obj) {x' x y y' : A.Obj}
    (a : (x' ⟶[SSet.{u}] x).obj (op ⦋0⦌))
    (b : (y ⟶[SSet.{u}] y').obj (op ⦋0⦌))
    [IsIso (classOfVertex D ((F.map x' x).app (op ⦋0⦌) a))]
    [IsIso (classOfVertex D ((F.map y y').app (op ⦋0⦌) b))]
    (h : GW (translation A a b)) : GW (F.map x' y') ↔ GW (F.map x y) := by
  have : WeakEquivalence (translation A a b) := (weakEquivalence_iff_GW _).2 h
  have : WeakEquivalence
      (translation D ((F.map x' x).app (op ⦋0⦌) a)
        ((F.map y y').app (op ⦋0⦌) b)) := translation_weakEquivalence D _ _
  constructor
  · intro h₁
    have : WeakEquivalence (F.map x' y') := (weakEquivalence_iff_GW _).2 h₁
    have : WeakEquivalence
        (F.map x y ≫ translation D ((F.map x' x).app (op ⦋0⦌) a)
          ((F.map y y').app (op ⦋0⦌) b)) := by
      rw [← translation_naturality F a b]
      infer_instance
    exact (weakEquivalence_iff_GW _).1 (weakEquivalence_of_postcomp (F.map x y)
      (translation D ((F.map x' x).app (op ⦋0⦌) a)
        ((F.map y y').app (op ⦋0⦌) b)))
  · intro h₀
    have : WeakEquivalence (F.map x y) := (weakEquivalence_iff_GW _).2 h₀
    have : WeakEquivalence (translation A a b ≫ F.map x' y') := by
      rw [translation_naturality F a b]
      infer_instance
    exact (weakEquivalence_iff_GW _).1 (weakEquivalence_of_precomp (translation A a b) (F.map x' y'))

/-- The mixed Hom projection compares the two diagonal endpoint Hom maps of a directed prism. -/
theorem endpoint_map_GW_iff
    (P : EnrichedFunctor SSet.{u} A.Obj B.Obj)
    (F : EnrichedFunctor SSet.{u} A.Obj D.Obj) {a₀ a₁ b₀ b₁ : A.Obj}
    (α : (a₀ ⟶[SSet.{u}] a₁).obj (op ⦋0⦌))
    (β : (b₀ ⟶[SSet.{u}] b₁).obj (op ⦋0⦌))
    [IsIso (classOfVertex B ((P.map a₀ a₁).app (op ⦋0⦌) α))]
    [IsIso (classOfVertex B ((P.map b₀ b₁).app (op ⦋0⦌) β))]
    [IsIso (classOfVertex D ((F.map a₀ a₁).app (op ⦋0⦌) α))]
    [IsIso (classOfVertex D ((F.map b₀ b₁).app (op ⦋0⦌) β))]
    (h₀₀ : GW (P.map a₀ b₀)) (h₀₁ : GW (P.map a₀ b₁))
    (h₁₁ : GW (P.map a₁ b₁)) : GW (F.map a₀ b₀) ↔ GW (F.map a₁ b₁) := by
  have : IsIso (classOfVertex B
      ((P.map a₀ a₀).app (op ⦋0⦌) (idVertex A a₀))) := mapped_id_class_isIso P a₀
  have : IsIso (classOfVertex D
      ((F.map a₀ a₀).app (op ⦋0⦌) (idVertex A a₀))) := mapped_id_class_isIso F a₀
  have : IsIso (classOfVertex B
      ((P.map b₁ b₁).app (op ⦋0⦌) (idVertex A b₁))) := mapped_id_class_isIso P b₁
  have : IsIso (classOfVertex D
      ((F.map b₁ b₁).app (op ⦋0⦌) (idVertex A b₁))) := mapped_id_class_isIso F b₁
  have hpost := translation_GW_of_projection P (idVertex A a₀) β h₀₀ h₀₁
  have hpre := translation_GW_of_projection P α (idVertex A b₁) h₁₁ h₀₁
  exact (map_GW_iff_translation F (idVertex A a₀) β hpost).symm.trans
    (map_GW_iff_translation F α (idVertex A b₁) hpre)

end
end DaggerActualEnrichedDirectedCylinder
