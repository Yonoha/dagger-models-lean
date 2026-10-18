/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
/-
Modified for dagger-models-lean from Joël Riou's topcat-model-category
commit 6c0c356fea469689fe76baeb47ba773460dfacee. Adapted to the pinned
Lean and Mathlib versions, including reuse of Mathlib's SSet.S API.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Simplices
import TopCatModelCategory.SSet.StandardSimplex

/-!
# The type of simplices of a simplicial set

In this file, we define the type `X.S` of simplices of a simplicial set `X`,
where a simplex consists of the data of `dim : ℕ` and `simplex : X _⦋dim⦌`.
We endow this type with a preorder defined by
`x ≤ y ↔ Subcomplex.ofSimplex x.simplex ≤ Subcomplex.ofSimplex y.simplex`.

## TODO (@joelriou)

* Extend the `S` structure to define the type of nondegenerate
simplices of a simplicial set `X`, and also the type of nondegenerate
simplices of a simplicial set `X` which do not belong to a given subcomplex.

-/

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

variable {X : SSet.{u}}

@[simp]
lemma Subcomplex.ofSimplex_map {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    (x : X _⦋m⦌) :
    ofSimplex (X.map f.op x) = ofSimplex x := by
  apply le_antisymm
  · rw [Subfunctor.ofSection_le_iff]
    exact ⟨_, rfl⟩
  · rw [Subfunctor.ofSection_le_iff]
    have := isSplitEpi_of_epi f
    exact ⟨(section_ f).op, by
      rw [← FunctorToTypes.map_comp_apply, ← op_comp,
        IsSplitEpi.id, op_id, FunctorToTypes.map_id_apply]⟩

namespace S

@[simp]
lemma mk_simplex (s : X.S) : S.mk s.simplex = s := rfl

@[simps!]
def toSubcomplex (x : X.S) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) : A.toSSet.S :=
  S.mk ⟨x.simplex, hx⟩

@[simp]
lemma map_dim {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S) : (S.map f s).dim = s.dim := rfl

@[simp]
lemma map_simplex {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S) :
    (S.map f s).simplex = f.app _ s.simplex := rfl

@[simp]
lemma map_toSubcomplex (x : X.S) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) :
    S.map A.ι (x.toSubcomplex hx) = x := rfl

lemma simplex_map_nonDegenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (s : X.S) :
    (S.map f s).simplex ∈ Y.nonDegenerate _ ↔ s.simplex ∈ X.nonDegenerate _ := by
  simp [S.map, nonDegenerate_iff_of_mono]

@[simp]
lemma map_id (s : X.S) : S.map (𝟙 _) s = s := rfl

lemma map_map {Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : X.S) :
    S.map g (S.map f s) = S.map (f ≫ g) s := rfl

lemma map_injective_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Function.Injective (S.map f) := by
  intro x y h
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl := S.dim_eq_of_mk_eq h
  simp only [ext_iff', map_dim, cast_dim, cast_simplex_rfl, map_simplex, exists_const] at h
  rw [ext_iff]
  exact (mono_iff_injective _).1 inferInstance h

/-- Compatibility for the old subcomplex-inclusion contract of `S.le_iff`. -/
lemma le_iff_subcomplex {x y : X.S} : x ≤ y ↔ x.subcomplex ≤ y.subcomplex :=
  S.le_def

@[simp]
lemma subcomplex_map {Y : SSet.{u}} (f : X ⟶ Y) (x : X.S) :
    (S.map f x).subcomplex = x.subcomplex.image f := by
  exact (Subcomplex.image_ofSimplex x.simplex f).symm

lemma toSubcomplex_le_toSubcomplex_iff
    (x y : X.S) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) (hy : y.simplex ∈ A.obj _) :
    x.toSubcomplex hx ≤ y.toSubcomplex hy ↔ x ≤ y := by
  simp only [le_iff_subcomplex, Subfunctor.ofSection_le_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, by rwa [Subtype.ext_iff] at hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, by rwa [Subtype.ext_iff]⟩

@[simp]
lemma map_ι_toSubcomplex (x : X.S) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) :
  S.map A.ι (x.toSubcomplex hx) = x := rfl

end S

end SSet
