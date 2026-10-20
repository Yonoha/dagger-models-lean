/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
/-
Modified for dagger-models-lean from Joël Riou's topcat-model-category
commit 6c0c356fea469689fe76baeb47ba773460dfacee. Adapted to the pinned
Lean and Mathlib versions, including changes to subcomplex API usage.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Adhesive
import TopCatModelCategory.ColimitsType
import TopCatModelCategory.CommSq
import TopCatModelCategory.SSet.Basic
import TopCatModelCategory.SSet.ChosenFiniteProducts

/-!
# Subcomplexes of simplicial sets

-/

universe u

open CategoryTheory MonoidalCategory Simplicial Limits Opposite

namespace CompleteLattice

open Classical in
abbrev CoproductDiagram {T ι : Type*} [CompleteLattice T] (A : T) (U : ι → T) :=
    MulticoequalizerDiagram A U (fun i j ↦ if i = j then U i else ⊥)

end CompleteLattice

/-namespace CategoryTheory
-- GrothendieckTopology.Subpresheaf should be moved...

variable {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*)

instance : CompleteLattice (Subpresheaf P) where
  sup F G :=
    { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h|h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h|h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf S T :=
    { obj U := S.obj U ⊓ T.obj U
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj U := sSup (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        obtain ⟨_, ⟨F, h, rfl⟩, h'⟩ := hx
        simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.preimage_iUnion,
          Set.mem_iUnion, Set.mem_preimage, exists_prop]
        exact ⟨_, h, F.map f h'⟩ }
  le_sSup _ _ _ _ _ := by aesop
  sSup_le _ _ _ _ _ := by aesop
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        rintro _ ⟨F, h, rfl⟩
        exact F.map f (hx _ ⟨_, h, rfl⟩) }
  sInf_le _ _ _ _ _ := by aesop
  le_sInf _ _ _ _ _ := by aesop
  bot :=
    { obj U := ⊥
      map := by simp }
  le_top _ _ := le_top
  bot_le _ _ := bot_le

namespace Subpresheaf

@[simp] lemma top_obj (i : Cᵒᵖ) : (⊤ : Subpresheaf P).obj i = ⊤ := rfl
@[simp] lemma bot_obj (i : Cᵒᵖ) : (⊥ : Subpresheaf P).obj i = ⊥ := rfl

variable {P}

lemma sSup_obj (S : Set (Subpresheaf P)) (U : Cᵒᵖ) :
    (sSup S).obj U = sSup (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
lemma iSup_obj {ι : Type*} (S : ι → Subpresheaf P) (U : Cᵒᵖ) :
    (iSup S).obj U = iSup (fun i ↦ (S i).obj U) := by
  simp [iSup, sSup_obj]

lemma sInf_obj (S : Set (Subpresheaf P)) (U : Cᵒᵖ) :
    (sInf S).obj U = sInf (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
lemma iInf_obj {ι : Type*} (S : ι → Subpresheaf P) (U : Cᵒᵖ) :
    (iInf S).obj U = iInf (fun i ↦ (S i).obj U) := by
  simp [iInf, sInf_obj]

lemma le_def (S T : Subpresheaf P) : S ≤ T ↔ ∀ U, S.obj U ≤ T.obj U := Iff.rfl

@[simp]
lemma max_obj (S T : Subpresheaf P) (i : Cᵒᵖ) :
    (S ⊔ T).obj i = S.obj i ∪ T.obj i := rfl

@[simp]
lemma min_obj (S T : Subpresheaf P) (i : Cᵒᵖ) :
    (S ⊓ T).obj i = S.obj i ∩ T.obj i := rfl

lemma max_min (S₁ S₂ T : Subpresheaf P) :
    (S₁ ⊔ S₂) ⊓ T = (S₁ ⊓ T) ⊔ (S₂ ⊓ T) := by
  aesop

lemma iSup_min {ι : Type*} (S : ι → Subpresheaf P) (T : Subpresheaf P) :
    iSup S ⊓ T = ⨆ i, S i ⊓ T := by
  aesop

end Subpresheaf

end CategoryTheory-/

namespace SSet

variable {X Y : SSet.{u}}

@[simp]
lemma braiding_hom_apply_fst {n : SimplexCategoryᵒᵖ} (x : (X ⊗ Y).obj n) :
    ((β_ X Y).hom.app n x).1 = x.2 := rfl

@[simp]
lemma braiding_hom_apply_snd {n : SimplexCategoryᵒᵖ} (x : (X ⊗ Y).obj n) :
    ((β_ X Y).hom.app n x).2 = x.1 := rfl

@[simp]
lemma braiding_inv_apply_fst {n : SimplexCategoryᵒᵖ} (x : (Y ⊗ X).obj n) :
    ((β_ X Y).inv.app n x).1 = x.2 := rfl

@[simp]
lemma braiding_inv_apply_snd {n : SimplexCategoryᵒᵖ} (x : (Y ⊗ X).obj n) :
    ((β_ X Y).inv.app n x).2 = x.1 := rfl

variable (X Y)

--protected abbrev Subcomplex := Subpresheaf X

namespace Subcomplex

/-instance : CompleteLattice X.Subcomplex :=
  inferInstance-/

variable {X Y}

variable (S : X.Subcomplex) (T : Y.Subcomplex)

--instance : CoeOut X.Subcomplex SSet.{u} where
--  coe := fun S ↦ S.toPresheaf

variable {S} in
lemma map_mem_obj {n m : SimplexCategoryᵒᵖ} (x : X.obj n) (f : n ⟶ m)
    (hx : x ∈ S.obj _) :
    X.map f x ∈ S.obj _ :=
  S.map f hx

variable (X)

variable {X}

/-variable {S} in
@[ext]
lemma coe_ext {Δ : SimplexCategoryᵒᵖ} {x y : S.obj Δ} (h : x.val = y.val) : x = y := by
  Subtype.ext h

lemma sSup_obj (S : Set X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    (sSup S).obj n = sSup (Set.image (fun T ↦ T.obj n) S) := rfl

@[simp]
lemma iSup_obj {ι : Type*} (S : ι → X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    (iSup S).obj n = iSup (fun i ↦ (S i).obj n) := by
  simp [iSup, sSup_obj]-/

lemma iSup_inf {ι : Type*} (S : ι → X.Subcomplex) (T : X.Subcomplex):
    (⨆ i, S i) ⊓ T = ⨆ i, (S i ⊓ T)  := by
  aesop

/-instance :
    letI src : SSet := S
    letI f : src ⟶ _ := S.ι
    Mono f := by
  change Mono S.ι
  infer_instance

@[simp]
lemma ι_app {Δ : SimplexCategoryᵒᵖ} (x : S.obj Δ) :
    S.ι.app Δ x = x.val := rfl-/

instance : Mono S.ι := by
  infer_instance


example : PartialOrder X.Subcomplex := inferInstance
example : SemilatticeSup X.Subcomplex := inferInstance

section

variable {S₁ S₂ : X.Subcomplex} (h : S₁ ≤ S₂)
end

@[simps]
def toPresheafFunctor : X.Subcomplex ⥤ SSet.{u} where
  obj S := S
  map h := homOfLE (leOfHom h)

section

variable {S₁ S₂ : X.Subcomplex} (h : S₁ = S₂)

@[simps]
def isoOfEq : (S₁ : SSet.{u}) ≅ (S₂ : SSet.{u}) where
  hom := homOfLE (by rw [h])
  inv := homOfLE (by rw [h])

end

variable (X) in
@[simps]
def forget : X.Subcomplex ⥤ SSet.{u} where
  obj S := S
  map f := homOfLE (leOfHom f)

noncomputable def unionProd : (X ⊗ Y).Subcomplex := ((⊤ : X.Subcomplex).prod T) ⊔ (S.prod ⊤)

lemma mem_unionProd_iff {n : SimplexCategoryᵒᵖ} (x : (X ⊗ Y).obj n) :
    x ∈ (unionProd S T).obj _ ↔ x.1 ∈ S.obj _ ∨ x.2 ∈ T.obj _ := by
  dsimp [unionProd, Set.prod]
  aesop

lemma top_prod_le_unionProd : (⊤ : X.Subcomplex).prod T ≤ S.unionProd T := le_sup_left

lemma prod_top_le_unionProd : (S.prod ⊤) ≤ S.unionProd T := le_sup_right

lemma prod_le_top_prod : S.prod T ≤ (⊤ : X.Subcomplex).prod T :=
  prod_monotone le_top (by rfl)

lemma prod_le_prod_top : S.prod T ≤ S.prod ⊤ :=
  prod_monotone (by rfl) le_top

lemma prod_le_unionProd : S.prod T ≤ S.unionProd T :=
  (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

end Subcomplex

/-def subcomplexBoundary (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ s := ¬Function.Surjective (stdSimplex.asOrderHom s)
  map φ s hs := ((boundary n).map φ ⟨s, hs⟩).2

lemma subcomplexBoundary_toSSet (n : ℕ) : subcomplexBoundary.{u} n = ∂Δ[n] := rfl

lemma subcomplexBoundary_ι (n : ℕ) :
    (subcomplexBoundary.{u} n).ι = boundaryInclusion n := rfl

@[simps]
def subcomplexHorn (n : ℕ) (i : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ s := Set.range (asOrderHom s) ∪ {i} ≠ Set.univ
  map φ s hs := ((horn n i).map φ ⟨s, hs⟩).2

lemma mem_subcomplexHorn_iff {n : ℕ} (i : Fin (n + 1)) {m : SimplexCategoryᵒᵖ}
    (x : (Δ[n] : SSet.{u}).obj m) :
    x ∈ (subcomplexHorn n i).obj m ↔ Set.range (asOrderHom x) ∪ {i} ≠ Set.univ := Iff.rfl

lemma subcomplexHorn_toSSet (n : ℕ) (i : Fin (n + 1)) :
    subcomplexHorn.{u} n i = Λ[n, i] := rfl

lemma subcomplexHorn_ι (n : ℕ) (i : Fin (n + 1)) :
    (subcomplexHorn.{u} n i).ι = hornInclusion n i := rfl-/

lemma mem_horn_iff {n : ℕ} (i : Fin (n + 1)) {m : SimplexCategoryᵒᵖ}
    (x : (Δ[n] : SSet.{u}).obj m) :
    x ∈ (horn n i).obj m ↔ Set.range (stdSimplex.asOrderHom x) ∪ {i} ≠ Set.univ := Iff.rfl

@[simp]
lemma boundary_zero : boundary.{u} 0 = ⊥ := by
  ext m x
  simp [boundary]
  intro x
  fin_cases x
  refine ⟨0, ?_⟩
  apply Subsingleton.elim

section

variable {X Y}
variable (f : X ⟶ Y)

attribute [local simp] FunctorToTypes.naturality

/-abbrev Subcomplex.range : Y.Subcomplex := Subpresheaf.range f

@[simps]
def Subcomplex.range : Y.Subcomplex where
  obj Δ := Set.range (f.app Δ)
  map := by
    rintro Δ Δ' φ _ ⟨x, rfl⟩
    exact ⟨X.map φ x, by simp⟩-/

@[simp]
lemma Subcomplex.range_ι (A : X.Subcomplex) :
    Subfunctor.range A.ι = A := by
  rw [Subfunctor.range_ι]

abbrev toRangeSubcomplex : X ⟶ Subcomplex.range f := Subfunctor.toRange f

@[simp]
lemma toRangeSubcomplex_apply_val {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) :
    ((toRangeSubcomplex f).app Δ x).val = f.app Δ x := rfl

@[reassoc (attr := simp)]
lemma toRangeSubcomplex_ι : toRangeSubcomplex f ≫ (Subcomplex.range f).ι = f := rfl

instance : Epi (toRangeSubcomplex f) := by
  change Epi (Subfunctor.toRange f)
  infer_instance

instance : Balanced SSet.{u} :=
  inferInstanceAs (Balanced (SimplexCategoryᵒᵖ ⥤ Type u))

instance {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] : IsIso (toRangeSubcomplex f) := by
  have := mono_of_mono_fac (toRangeSubcomplex_ι f)
  apply isIso_of_mono_of_epi

end

namespace Subcomplex

variable {X}
attribute [simp] preimage_eq_top_iff
def Sq (A₁ A₂ A₃ A₄ : X.Subcomplex) := Lattice.BicartSq A₁ A₂ A₃ A₄

namespace Sq

variable {A₁ A₂ A₃ A₄ : X.Subcomplex} (sq : Sq A₁ A₂ A₃ A₄)

include sq

lemma le₁₂ : A₁ ≤ A₂ := by rw [← sq.inf_eq]; exact inf_le_left
lemma le₁₃ : A₁ ≤ A₃ := by rw [← sq.inf_eq]; exact inf_le_right
lemma le₂₄ : A₂ ≤ A₄ := by rw [← sq.sup_eq]; exact le_sup_left
lemma le₃₄ : A₃ ≤ A₄ := by rw [← sq.sup_eq]; exact le_sup_right

-- the associated commutative square in `SSet`, which is both pushout and pullback
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

lemma obj (n : SimplexCategoryᵒᵖ) :
    Lattice.BicartSq (A₁.obj n) (A₂.obj n) (A₃.obj n) (A₄.obj n) where
  sup_eq := by
    rw [← sq.sup_eq]
    rfl
  inf_eq := by
    rw [← sq.inf_eq]
    rfl

lemma isPushout : IsPushout (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) where
  w := rfl
  isColimit' := ⟨by
    refine evaluationJointlyReflectsColimits _ (fun n ↦ ?_)
    exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (Types.isColimitPushoutCoconeOfBicartSqOfSets (sq.obj n))⟩

end Sq

section

lemma ofSimplex_eq_range {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    Subcomplex.ofSimplex x = range (yonedaEquiv.symm x) := by
  simp only [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]

lemma mem_ofSimplex₀_obj_iff {X : SSet.{u}} (x : X _⦋0⦌) {n : SimplexCategory} (y : X.obj (op n)) :
    y ∈ (Subcomplex.ofSimplex x).obj _ ↔ y = X.map (n.const ⦋0⦌ 0).op x := by
  simp only [ofSimplex, Subfunctor.ofSection, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨f⟩, rfl⟩
    obtain rfl := Subsingleton.elim f (n.const ⦋0⦌ 0)
    rfl
  · tauto

@[simp]
lemma preimage_ι {X : SSet.{u}} (A : X.Subcomplex) :
    A.preimage A.ι = ⊤ := by
  aesop

@[simp]
lemma range_const_ι {X Y : SSet.{u}} (y : Y _⦋0⦌) :
    (range (const y : X ⟶ Y)).ι = const y := by
  ext ⟨n⟩ ⟨_, x, rfl⟩
  simp

/-def ofSimplex {n : ℕ} (x : X _[n]) : X.Subcomplex :=
  range ((X.yonedaEquiv (.mk n)).symm x)-/

--@[simp]
--lemma range_eq_ofSimplex {n : ℕ} (f : Δ[n] ⟶ X) :
--    range f = ofSimplex (X.yonedaEquiv _ f) := by
--  simp [ofSimplex]

/-lemma mem_ofSimplex_obj {n : ℕ} (x : X _[n]) : x ∈ (ofSimplex x).obj _ := by
  refine ⟨standardSimplex.objMk .id, ?_⟩
  obtain ⟨x, rfl⟩ := (X.yonedaEquiv _).surjective x
  rw [Equiv.symm_apply_apply]
  rfl

lemma ofSimplex_le_iff {n : ℕ} (x : X _[n]) (A : X.Subcomplex) :
    ofSimplex x ≤ A ↔ x ∈ A.obj _ := by
  constructor
  · intro h
    apply h
    apply mem_ofSimplex_obj
  · rintro h m _ ⟨y, rfl⟩
    obtain ⟨f, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective y
    exact A.map f.op h

lemma mem_ofSimplex_obj_iff {n : ℕ} (x : X _⦋n⦌) {m : SimplexCategoryᵒᵖ} (y : X.obj m) :
    y ∈ (ofSimplex x).obj m ↔ ∃ (f : m.unop ⟶ ⦋n⦌), X.map f.op x = y := by
  simp [ofSimplex, Subpresheaf.ofSection]
  aesop-/

lemma le_ofSimplex_iff (x : X _⦋0⦌) (A : X.Subcomplex) :
    A ≤ ofSimplex x ↔ A.ι = const x := by
  constructor
  · intro h
    ext m ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := h _ hx
    obtain rfl : f = (SimplexCategory.const _ _ 0).op := Quiver.Hom.unop_inj (by aesop)
    simp
  · intro h
    simp only [← A.range_ι, h]
    rintro m _ ⟨y, rfl⟩
    rw [const_app]
    exact Subfunctor.map _ _ (mem_ofSimplex_obj x)

end

section

variable {Y} (S : X.Subcomplex) (f : X ⟶ Y)

end

section

lemma _root_.Set.preimage_eq_iff {X Y : Type*} (f : X → Y)
    (hf : Function.Injective f) (A : Set X) (B : Set Y) :
    B.preimage f = A ↔ B ⊓ Set.range f = A.image f := by
  constructor
  · aesop
  · intro h
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hx⟩ : f x ∈ f '' A := by
        rw [← h]
        exact ⟨hx, by aesop⟩
      simpa only [← hf hx] using hy
    · intro hx
      have : f '' A ≤ B := by
        rw [← h]
        exact inf_le_left
      apply this
      aesop

lemma preimage_eq_iff {X Y : SSet.{u}}
    (f : X ⟶ Y) (A : X.Subcomplex) (B : Y.Subcomplex) [Mono f] :
    B.preimage f = A ↔ B ⊓ Subcomplex.range f = A.image f := by
  simp only [Subfunctor.ext_iff, funext_iff]
  apply forall_congr'
  intro i
  apply Set.preimage_eq_iff
  rw [← mono_iff_injective]
  infer_instance


@[simp]
lemma preimage_image_of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) (B : Y.Subcomplex) [IsIso f] :
    (B.preimage f).image f = B := by
  apply le_antisymm
  · rw [image_le_iff]
  · intro n y hy
    exact ⟨(inv f).app _ y, by simpa [← FunctorToTypes.comp]⟩

end

section

variable {Y} (f : X ⟶ Y) {B : Y.Subcomplex} (hf : B.preimage f = ⊤)

def liftFromPreimage : X ⟶ B :=
  (topIso X).inv ≫ homOfLE (by simp [hf]) ≫ B.fromPreimage f

@[reassoc (attr := simp)]
lemma liftFromPreimage_ι : liftFromPreimage f hf ≫ B.ι = f := rfl

@[simp]
lemma liftFromPreimage_app_coe {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    ((liftFromPreimage f g).app _ x).1 = f.app _ x := rfl

lemma liftFromPreimage_eq_lift :
    liftFromPreimage f hf = Subcomplex.lift f ((preimage_eq_top_iff B f).1 hf) := rfl

end

section

variable {n : ℕ} (x : X _⦋n⦌)

def toOfSimplex : Δ[n] ⟶ ofSimplex x :=
  Subcomplex.liftFromPreimage (yonedaEquiv.symm x) (by
    apply le_antisymm (by simp)
    simp only [← image_le_iff, image_top, range_eq_ofSimplex,
      Equiv.apply_symm_apply, le_refl])

@[reassoc (attr := simp)]
lemma toOfSimplex_ι :
    toOfSimplex x ≫ (ofSimplex x).ι = yonedaEquiv.symm x := rfl

@[simp]
lemma yonedaEquiv_toOfSimplex :
    yonedaEquiv (toOfSimplex x) = ⟨x, mem_ofSimplex_obj x⟩ := by
  apply yonedaEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

instance : Epi (toOfSimplex x) := by
  rw [← range_eq_top_iff]
  ext m ⟨_, u, rfl⟩
  simp only [Subfunctor.toFunctor_obj, range_eq_ofSimplex, Subfunctor.top_obj, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  refine ⟨u, ?_⟩
  dsimp
  ext
  conv_rhs => rw [← yonedaEquiv.right_inv x]
  rfl

lemma isIso_toOfSimplex_iff :
    IsIso (toOfSimplex x) ↔ Mono (yonedaEquiv.symm x) := by
  constructor
  · intro
    rw [← toOfSimplex_ι]
    infer_instance
  · intro h
    have := mono_of_mono_fac (toOfSimplex_ι x)
    apply isIso_of_mono_of_epi

end

section

variable {Y} (f : Y ⟶ X) (A B : X.Subcomplex) (A' B' : Y.Subcomplex)
    (hA' : A' = A.preimage f ⊓ B')
    (hB : B = A ⊔ B'.image f)

namespace pushoutCoconeOfPullback

variable {f A A' B'}

@[simps!]
def g₁ : (A' : SSet) ⟶ (A : SSet) :=
  homOfLE (by simpa only [hA'] using inf_le_left) ≫ A.fromPreimage f

@[simps!]
def g₂ : (A' : SSet) ⟶ (B' : SSet) :=
  homOfLE (by simpa only [hA'] using inf_le_right)

end pushoutCoconeOfPullback

open pushoutCoconeOfPullback

@[simps!]
def pushoutCoconeOfPullback : PushoutCocone (g₁ hA') (g₂ hA') :=
  PushoutCocone.mk (W := (B : SSet)) (homOfLE (by simpa only [hB] using le_sup_left))
    (homOfLE (by simpa only [← image_le_iff, hB] using le_sup_right) ≫ B.fromPreimage f) rfl

noncomputable def isColimitPushoutCoconeOfPullback [hf : Mono f] :
    IsColimit (pushoutCoconeOfPullback f A B A' B' hA' hB) :=
  evaluationJointlyReflectsColimits _ (fun n ↦
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (Types.isColimitPushoutCoconeOfPullbackSets (f := f.app n)
      (A.obj n) (B.obj n) (A'.obj n) (B'.obj n) (by rw [hA']; rfl) (by rw [hB]; rfl)
        (by
          rw [NatTrans.mono_iff_mono_app] at hf
          simp only [mono_iff_injective] at hf
          rintro ⟨x₁, _⟩ ⟨x₂, _⟩ h
          simpa only [Subtype.mk.injEq] using hf n h)))

end

variable {Y} in
noncomputable def prodIso (S : X.Subcomplex) (T : Y.Subcomplex) :
    (S.prod T : SSet) ≅ (S : SSet) ⊗ (T : SSet) where
  hom := CartesianMonoidalCategory.lift
    (liftFromPreimage ((S.prod T).ι ≫ CartesianMonoidalCategory.fst _ _) (by
      ext n ⟨x, h⟩
      simpa using h.1))
    (liftFromPreimage ((S.prod T).ι ≫ CartesianMonoidalCategory.snd _ _) (by
      ext n ⟨x, h⟩
      simpa using h.2))
  inv := liftFromPreimage (S.ι ⊗ₘ T.ι) (by
    ext n ⟨x, y⟩
    dsimp
    simp only [Set.mem_preimage, tensorHom_app_apply, Subfunctor.ι_app,
      Set.mem_univ, iff_true]
    exact ⟨x.2, y.2⟩)

namespace unionProd

variable {Y} (S : X.Subcomplex) (T : Y.Subcomplex)

noncomputable def ι₁ : X ⊗ T ⟶ unionProd S T :=
  liftFromPreimage (X ◁ T.ι) (by
    ext m ⟨x₁, x₂⟩
    simp [unionProd, Set.prod]
    exact Or.inl x₂.2)

noncomputable def ι₂ : (S : SSet.{u}) ⊗ Y ⟶ (unionProd S T : SSet.{u}) :=
  liftFromPreimage (S.ι ▷ Y) (by
    ext m ⟨x₁, x₂⟩
    simp [unionProd, Set.prod]
    exact Or.inr x₁.2)

@[reassoc (attr := simp)]
lemma ι₁_ι : ι₁ S T ≫ (unionProd S T).ι = X ◁ T.ι := rfl

@[reassoc (attr := simp)]
lemma ι₂_ι : ι₂ S T ≫ (unionProd S T).ι = S.ι ▷ Y := rfl

lemma sq : Sq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where
  sup_eq := rfl
  inf_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, setOf]
    tauto

lemma isPushout : IsPushout (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι)
    (unionProd.ι₁ S T) (unionProd.ι₂ S T) :=
  (sq S T).isPushout.of_iso
    (Subcomplex.prodIso _ _)
    (Subcomplex.prodIso _ _ ≪≫ MonoidalCategory.whiskerRightIso (topIso X) _)
    (Subcomplex.prodIso _ _ ≪≫ MonoidalCategory.whiskerLeftIso _ (topIso Y))
    (Iso.refl _) rfl rfl rfl rfl

@[simp]
lemma preimage_β_hom : (unionProd S T).preimage (β_ _ _).hom = unionProd T S := by
  ext n ⟨x, y⟩
  simp only [mem_unionProd_iff, preimage_obj, Set.mem_preimage,
    braiding_hom_apply_fst, braiding_hom_apply_snd]
  tauto

@[simp]
lemma preimage_β_inv : (unionProd S T).preimage (β_ _ _).inv = unionProd T S := by
  apply preimage_β_hom

@[simp]
lemma image_β_hom : (unionProd S T).image (β_ _ _).hom = unionProd T S := by
  rw [← preimage_β_hom, preimage_image_of_isIso]

@[simp]
lemma image_β_inv : (unionProd S T).image (β_ _ _).hom = unionProd T S := by
  apply image_β_hom


noncomputable def symmIso : (unionProd S T : SSet) ≅ (unionProd T S : SSet) where
  hom := liftFromPreimage ((unionProd S T).ι ≫ (β_ _ _).hom) (by
    simp only [Subcomplex.preimage_eq_top_iff, range_comp, Subfunctor.range_ι, image_β_hom,
      le_refl])
  inv := liftFromPreimage ((unionProd T S).ι ≫ (β_ _ _).hom) (by
    simp only [Subcomplex.preimage_eq_top_iff, range_comp, Subfunctor.range_ι, image_β_hom,
      le_refl])

end unionProd

section multicoequalizer

variable {A : X.Subcomplex} {ι : Type*}
  {U : ι → X.Subcomplex} {V : ι → ι → X.Subcomplex}
  (h : CompleteLattice.MulticoequalizerDiagram A U V)

noncomputable def multicoforkIsColimit :
    IsColimit (h.multicofork.map toPresheafFunctor) :=
  evaluationJointlyReflectsColimits _ (fun n ↦ by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i ↦ (U i).obj n)
        (fun i j ↦ (V i j).obj n) :=
      { eq_inf := by simp [h.eq_inf]
        iSup_eq := by simp [← h.iSup_eq] }
    exact (Multicofork.isColimitMapEquiv _ _).2 (Types.isColimitMulticoforkMapSetToTypes h'))

noncomputable def multicoforkIsColimit' [LinearOrder ι] :
    IsColimit (h.multicofork.toLinearOrder.map toPresheafFunctor) :=
  Multicofork.isColimitToLinearOrder _ (multicoforkIsColimit h)
    { iso i j := toPresheafFunctor.mapIso (eqToIso (by
        dsimp
        rw [h.eq_inf, h.eq_inf, inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

end multicoequalizer

section

variable {Y}

@[ext]
lemma hom_ext (B : Y.Subcomplex) {f g : X ⟶ B} (h : f ≫ B.ι = g ≫ B.ι) : f = g := by
  simpa only [cancel_mono] using h

lemma hom_ext_of_eq_bot {A : X.Subcomplex} (h : A = ⊥) {f g : (A : SSet) ⟶ Y} : f = g := by
  ext _ ⟨x, hx⟩
  simp [h] at hx

end

lemma preimage_preimage {X Y Z : SSet.{u}} (A : Z.Subcomplex) (f : X ⟶ Y) (g : Y ⟶ Z) :
    A.preimage (f ≫ g) = (A.preimage g).preimage f := rfl

lemma preimage_ι_comp_eq_top_iff {X Y : SSet.{u}} (B : Y.Subcomplex) (A : X.Subcomplex) (f : X ⟶ Y) :
    B.preimage (A.ι ≫ f) = ⊤ ↔ A ≤ B.preimage f := by
  simp only [← top_le_iff, preimage_preimage, ← Subcomplex.image_le_iff, image_top,
    Subfunctor.range_ι]

section

variable {X : SSet.{u}} {A B : X.Subcomplex} (h : A = B)

@[reassoc (attr := simp)]
lemma isoOfEq_hom_ι : (isoOfEq h).hom ≫ B.ι = A.ι := rfl

@[reassoc (attr := simp)]
lemma isoOfEq_inv_ι : (isoOfEq h).inv ≫ A.ι = B.ι := rfl

end

@[simp]
lemma iSup_obj {ι : Sort*} (S : ι → X.Subcomplex) (U : SimplexCategoryᵒᵖ) :
    (⨆ i, S i).obj U = ⋃ i, (S i).obj U := by
  simp [iSup, Subfunctor.sSup_obj]

instance : Subsingleton ((⊥ : X.Subcomplex).toSSet ⟶ Y) where
  allEq f g := by
    ext _ ⟨x, hx⟩
    simp at hx

instance : Inhabited ((⊥ : X.Subcomplex).toSSet ⟶ Y) where
  default :=
    { app _ := fun ⟨_, hx⟩ ↦ by simp at hx
      naturality _ _ _ := by
        ext ⟨_, hx⟩
        simp at hx }

instance : Unique ((⊥ : X.Subcomplex).toSSet ⟶ Y) where
  uniq _ := Subsingleton.elim _ _

def botIsInitial : IsInitial (⊥ : X.Subcomplex).toSSet :=
  IsInitial.ofUnique _

section coproducts

variable {ι : Type*} {U : ι → X.Subcomplex}

section

variable {A : X.Subcomplex} (h : CompleteLattice.CoproductDiagram A U)

abbrev cofan : Cofan (fun i ↦ (U i : SSet)) :=
  Cofan.mk A (fun i ↦ homOfLE (by rw [← h.iSup_eq]; apply le_iSup))

noncomputable def isColimitCofan : IsColimit (cofan h) :=
  mkCofanColimit _
    (fun s ↦ (multicoforkIsColimit h).desc
      (Multicofork.ofπ _ s.pt (fun i ↦ s.inj i) (fun ⟨i, j⟩ ↦ by
        by_cases hij : i = j
        · subst hij
          rfl
        · apply IsInitial.hom_ext
          dsimp
          rw [if_neg hij]
          exact botIsInitial)))
    (fun s i ↦ (multicoforkIsColimit h).fac _ (.right i))
    (fun s m hm ↦ by
      apply Multicofork.IsColimit.hom_ext (multicoforkIsColimit h)
      intro i
      exact (hm i).trans ((multicoforkIsColimit h).fac
        (Multicofork.ofπ _ s.pt (fun i ↦ s.inj i) _) (.right i)).symm)

end

variable (h : CompleteLattice.CoproductDiagram ⊤ U)

variable (U) in
abbrev cofan' : Cofan (fun i ↦ (U i : SSet)) :=
  Cofan.mk X (fun i ↦ (U i).ι)

noncomputable def isColimitCofan' : IsColimit (cofan' U) :=
  IsColimit.ofIsoColimit (isColimitCofan h) (Cofan.ext (topIso X) (fun i ↦ by simp))

end coproducts

variable {Y}

@[simp]
lemma preimage_image_of_mono (S : X.Subcomplex) (f : X ⟶ Y) [Mono f] :
    (S.image f).preimage f = S := by
  apply le_antisymm
  · intro n x hx
    simp only [preimage_obj, Set.mem_preimage] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    obtain rfl : y = x := (mono_iff_injective _).1 inferInstance hxy
    exact hy
  · rw [← image_le_iff]

@[simp]
lemma image_le_image_iff_of_mono (f : X ⟶ Y) (S T : X.Subcomplex) [Mono f] :
    S.image f ≤ T.image f ↔ S ≤ T := by
  rw [image_le_iff, preimage_image_of_mono]


@[simps! hom_left hom_right hom_right inv_right]
def congrArrowι (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex}
    (h : A.image e.hom = B) :
    Arrow.mk A.ι ≅ Arrow.mk B.ι :=
  Arrow.isoMk
    { hom := Subcomplex.liftFromPreimage (A.ι ≫ e.hom)
        (le_antisymm (by simp) (by simp [range_comp, h]))
      inv := Subcomplex.liftFromPreimage (B.ι ≫ e.inv)
        (le_antisymm (by simp) (by
          have h' : B.image e.inv = A := by
            rw [← h, ← image_comp, e.hom_inv_id, image_id]
          simp [range_comp, h']))
      hom_inv_id := by simp [← cancel_mono A.ι]
      inv_hom_id := by simp [← cancel_mono B.ι] } e

@[simps! hom_left hom_right hom_right inv_right]
def congrArrowι' (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex}
    (h : B.preimage e.hom = A) :
    Arrow.mk A.ι ≅ Arrow.mk B.ι :=
  congrArrowι e (by simp [← h])

end Subcomplex

end SSet
