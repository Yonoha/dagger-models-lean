import TopCatModelCategory.SSet.Simplices
import TopCatModelCategory.SSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices

universe u

open CategoryTheory Simplicial Limits Opposite

/-@[simp]
lemma SSet.id_app {X : SSet.{u}} {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    NatTrans.app (𝟙 X) n x = x := rfl-/

lemma Quiver.Hom.op_surjective {C : Type*} [Quiver C] {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃ (g : Y.unop ⟶ X.unop), f = g.op := ⟨f.unop, rfl⟩

instance {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    IsSplitMono f.op where
  exists_splitMono := ⟨⟨(section_ f).op, Quiver.Hom.unop_inj (by simp)⟩⟩

lemma SimplexCategory.isIso_iff_len_eq_of_epi {n m : SimplexCategory} (f : n ⟶ m) [Epi f] :
    IsIso f ↔ n.len = m.len := by
  have hf := len_le_of_epi f
  refine ⟨fun _ ↦ le_antisymm (len_le_of_mono f) hf, fun h ↦ ?_⟩
  obtain rfl : n = m := by aesop
  have h := (epi_iff_surjective (f := f)).1 inferInstance
  exact isIso_of_bijective ⟨by rwa [Finite.injective_iff_surjective], h⟩

lemma SimplexCategory.exists_mono_fac {n m : SimplexCategory} (f : n ⟶ m) :
    ∃ (d : ℕ) (p : n ⟶ ⦋d⦌) (i : ⦋d⦌ ⟶ m), Epi p ∧ Mono i ∧ p ≫ i = f := by
  suffices ∃ (d : SimplexCategory) (p : n ⟶ d) (i : d ⟶ m), Epi p ∧ Mono i ∧ p ≫ i = f by
    obtain ⟨d, p, i, _, _, fac⟩ := this
    induction d using SimplexCategory.rec with | _ d
    exact ⟨d, p, i, inferInstance, inferInstance, fac⟩
  exact ⟨_, _, _, inferInstance, inferInstance, image.fac f⟩

namespace SSet

variable (X : SSet.{u})

namespace N

variable {X}

/-- Compatibility name for the original structure constructor. -/
abbrev mk'' (s : X.S) (hs : s.simplex ∈ X.nonDegenerate _) : X.N := N.mk' s hs

@[simp]
lemma mk'_toS (s : X.S) (hs : s.simplex ∈ X.nonDegenerate _) :
    (N.mk' s hs).toS = s := rfl

@[deprecated (since := "2025-08-06")] alias exists_nonDegenerate := mk_surjective

lemma induction
    {motive : ∀ {n : ℕ} (x : X _⦋n⦌) (_ : x ∈ X.nonDegenerate _), Prop}
    (h₁ : ∀ (x : X.N), motive x.1.2 x.2)
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate _) : motive x hx :=
  h₁ (mk x hx)

lemma le_iff_toS_le_toS {x y : X.N} : x ≤ y ↔ x.toS ≤ y.toS := Iff.rfl

lemma le_iff_exists {x y : X.N} :
    x ≤ y ↔ ∃ (f : ⦋x.1.1⦌ ⟶ ⦋y.1.1⦌) (_ : Mono f), X.map f.op y.1.2 = x.1.2 := by
  simp only [le_iff, CategoryTheory.Subfunctor.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  refine ⟨?_, by tauto⟩
  rintro ⟨f, hf⟩
  refine ⟨f, ?_, hf⟩
  have : IsIso (factorThruImage f) := by
    rw [SimplexCategory.isIso_iff_len_eq_of_epi]
    obtain h | h := (SimplexCategory.len_le_of_epi
      (factorThruImage f)).eq_or_lt
    · exact h.symm
    · exfalso
      apply (mem_nonDegenerate_iff_notMem_degenerate _ _).1 x.2
      rw [mem_degenerate_iff]
      refine ⟨_, h, factorThruImage f, inferInstance, ?_⟩
      rw [← image.fac f, op_comp, FunctorToTypes.map_comp_apply] at hf
      rw [← hf]
      apply Set.mem_range_self
  have := isIso_of_mono_of_epi (factorThruImage f)
  rw [← image.fac f]
  infer_instance

lemma le_of_le {x y : X.N} (h : x ≤ y) : x.1.1 ≤ y.1.1 := by
  rw [le_iff_exists] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono f

lemma lt_of_lt {x y : X.N} (h : x < y) : x.dim < y.dim := by
  obtain h' | h' := (le_of_le h.le).lt_or_eq
  · exact h'
  · have h'' := h.le
    rw [le_iff_exists] at h''
    obtain ⟨d, ⟨x, hx⟩, rfl⟩ := x.mk_surjective
    obtain ⟨d', ⟨y, hy⟩, rfl⟩ := y.mk_surjective
    obtain rfl : d = d' := h'
    obtain ⟨f, _, hf⟩ := h''
    obtain rfl := SimplexCategory.eq_id_of_mono f
    obtain rfl : x = y := by simpa using hf.symm
    simp at h

def toSubcomplex (x : X.N) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) : A.toSSet.N :=
  N.mk' (x.toS.toSubcomplex hx) (by
    rw [Subcomplex.mem_nonDegenerate_iff]
    exact x.nonDegenerate)

lemma toS_toSubcomplex (x : X.N) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) :
    (x.toSubcomplex hx).toS = x.toS.toSubcomplex hx := rfl

lemma toSubcomplex_le_toSubcomplex_iff
    (x y : X.N) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) (hy : y.simplex ∈ A.obj _) :
    x.toSubcomplex hx ≤ y.toSubcomplex hy ↔ x ≤ y := by
  apply S.toSubcomplex_le_toSubcomplex_iff

@[ext]
lemma ext {x y : X.N} (h : x.toS = y.toS) :
    x = y := by
  rwa [ext_iff]

lemma mk_eq_iff_sMk_eq {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌)
    (hx : x ∈ X.nonDegenerate _) (hy : y ∈ X.nonDegenerate _) :
    N.mk x hx = N.mk y hy ↔ S.mk x = S.mk y := by
  rw [ext_iff]
  rfl

end N

@[simps! obj]
def functorN : X.N ⥤ SSet.{u} :=
  X.orderEmbeddingN.monotone.functor ⋙ Subcomplex.toPresheafFunctor

variable {X} in
@[simp]
lemma functorN_map {x₁ x₂ : X.N} (f : x₁ ⟶ x₂) :
    X.functorN.map f = Subcomplex.homOfLE (X.orderEmbeddingN.monotone (leOfHom f)) := rfl

namespace S

variable {X}

lemma subcomplex_eq_of_epi (x y : X.S) (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) [Epi f]
    (hf : X.map f.op y.simplex = x.simplex) :
    x.subcomplex = y.subcomplex := by
  refine le_antisymm ?_ ?_
  · simp only [Subcomplex.ofSimplex_le_iff]
    exact ⟨f.op, by aesop⟩
  · simp only [Subcomplex.ofSimplex_le_iff]
    have := isSplitEpi_of_epi f
    have : Function.Injective (X.map f.op) := by
      rw [← mono_iff_injective]
      infer_instance
    refine ⟨(section_ f).op, this ?_⟩
    dsimp
    rw [← hf, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
      ← op_comp, ← op_comp, Category.assoc, IsSplitEpi.id, Category.comp_id]

lemma toN_of_nonDegenerate (x : X.S) (hx : x.simplex ∈ X.nonDegenerate _) :
    x.toN = N.mk _ hx := by
  rw [toN_eq_iff]
  rfl

lemma existsUnique_toNπ' {x : X.S} {y : X.N} (hy : x.toN = y) :
    ∃! (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌), Epi f ∧ X.map f.op y.simplex = x.simplex := by
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective
  obtain ⟨m, f, _, z, rfl⟩ := X.exists_nonDegenerate x
  obtain rfl : y = N.mk _ z.2 := by
    rw [toN_eq_iff] at hy
    rw [← N.subcomplex_injective_iff, hy]
    exact subcomplex_eq_of_epi _ _ f rfl
  exact existsUnique_of_exists_of_unique ⟨f, inferInstance, rfl⟩
    (fun f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩ ↦ unique_nonDegenerate_map _ _ _ _ hf₁.symm _ _ hf₂.symm)

section

variable {x : X.S} {y : X.N} (hy : x.toN = y)

noncomputable def toNπ' {x : X.S} {y : X.N} (hy : x.toN = y) : ⦋x.dim⦌ ⟶ ⦋y.dim⦌ :=
  (existsUnique_toNπ' hy).exists.choose

instance : Epi (toNπ' hy) := (existsUnique_toNπ' hy).exists.choose_spec.1

@[simp]
lemma map_toNπ' : X.map (toNπ' hy).op y.simplex = x.simplex :=
  (existsUnique_toNπ' hy).exists.choose_spec.2

lemma dim_toN_le (x : X.S) : x.toN.dim ≤ x.dim :=
  SimplexCategory.le_of_epi (toNπ' (x := x) rfl)

lemma toNπ'_eq_iff (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) :
    toNπ' hy = f ↔ X.map f.op y.simplex = x.simplex := by
  constructor
  · rintro rfl
    simp
  · intro hf
    refine (existsUnique_toNπ' hy).unique ⟨inferInstance, by simp⟩
      ⟨?_, hf⟩
    obtain ⟨d, p, i, _, _, fac⟩ := SimplexCategory.exists_mono_fac f
    obtain h | rfl := (SimplexCategory.le_of_mono i).lt_or_eq
    · exfalso
      let z := S.mk (X.map i.op y.simplex)
      have h₁ : z.toN = y := by
        rw [toN_eq_iff]
        apply le_antisymm
        · rw [← hy, x.subcomplex_toN, Subfunctor.ofSection_le_iff]
          exact ⟨p.op, by simp [← hf, ← fac, z]⟩
        · rw [Subfunctor.ofSection_le_iff]
          exact ⟨i.op, rfl⟩
      have h₂ := z.dim_toN_le
      rw [N.ext_iff] at h₁
      rw [S.dim_eq_of_eq h₁] at h₂
      simpa [z] using lt_of_lt_of_le h h₂
    · obtain rfl := SimplexCategory.eq_id_of_mono i
      simpa [← fac]

end

noncomputable def toNπ (x : X.S) : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌ := toNπ' rfl

instance (x : X.S) : Epi x.toNπ := by dsimp [toNπ]; infer_instance

@[simp]
lemma map_toNπ (x : X.S) : X.map x.toNπ.op x.toN.simplex = x.simplex := by
  simp [toNπ]

lemma toNπ_eq_iff (x : X.S) (f : ⦋x.dim⦌ ⟶ ⦋x.toN.dim⦌) :
    x.toNπ = f ↔ X.map f.op x.toN.simplex = x.simplex := by
  apply toNπ'_eq_iff

lemma self_le_toS_toN (s : X.S) : s ≤ s.toN.toS := by
  rw [S.le_iff_subcomplex, subcomplex_toN]

lemma toS_toN_le_self (s : X.S) : s.toN.toS ≤ s := by
  rw [S.le_iff_subcomplex, subcomplex_toN]

end S

variable {X}

@[simp]
lemma N.toS_toN (x : X.N) : x.toS.toN = x := by
  rw [S.toN_eq_iff]

lemma N.toN_surjective : Function.Surjective (S.toN (X := X)) :=
  fun s ↦ ⟨s.toS, by simp⟩

variable (X)

@[simps]
def coconeN : Cocone X.functorN where
  pt := X
  ι := { app _ := Subcomplex.ι _ }

namespace isColimitCoconeN

variable {X}

lemma hom_ext {Y : SSet.{u}} {f g : X ⟶ Y}
    (h : ∀ (x : X.N), (Subcomplex.ofSimplex x.1.2).ι ≫ f = (Subcomplex.ofSimplex x.1.2).ι ≫ g) :
    f = g := by
  rw [← cancel_epi (Subcomplex.topIso _).hom, ← Subfunctor.equalizer_eq_iff,
    Subcomplex.eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simpa [Subfunctor.equalizer] using
    congr_fun (NatTrans.congr_app (h (N.mk _ hx)) (op ⦋n⦌))
      ⟨x, Subcomplex.mem_ofSimplex_obj x⟩

variable (s : Cocone X.functorN)

noncomputable def descApp {n : ℕ} (x : X _⦋n⦌) : s.pt _⦋n⦌ :=
  yonedaEquiv (stdSimplex.map (S.mk x).toNπ ≫ Subcomplex.toOfSimplex _ ≫ s.ι.app (S.mk x).toN)

lemma descApp_apply {n : ℕ} (x : X _⦋n⦌) (y : X.N) (f : ⦋n⦌ ⟶ ⦋y.1.1⦌) [Epi f]
    (hf : X.map f.op y.1.2 = x) :
    descApp s x = yonedaEquiv (stdSimplex.map f ≫ Subcomplex.toOfSimplex _ ≫ s.ι.app y) := by
  obtain rfl : (S.mk x).toN = y := by
    rw [S.toN_eq_iff, ← hf]
    exact (S.subcomplex_eq_of_epi _ _ f rfl).symm
  dsimp only [descApp]
  congr
  rwa [S.toNπ_eq_iff]

@[simp]
lemma descApp_apply' (x : X.N) :
    descApp s x.1.2 = (s.ι.app x).app _ ⟨x.1.2, Subcomplex.mem_ofSimplex_obj _⟩ :=  by
  rw [descApp_apply s x.1.2 x (𝟙 _) (by simp), CategoryTheory.Functor.map_id, Category.id_comp,
    yonedaEquiv_comp, Subcomplex.yonedaEquiv_toOfSimplex]

noncomputable def desc : X ⟶ s.pt where
  app := fun ⟨n⟩ ↦ by
    induction n using SimplexCategory.rec with | _ n
    exact descApp _
  naturality := by
    rintro ⟨n⟩ ⟨m⟩ f
    obtain ⟨f, rfl⟩ := Quiver.Hom.op_surjective f
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    dsimp [SimplexCategory.rec]
    ext x
    dsimp [descApp]
    have h : (S.mk (X.map f.op x)).toN ≤ (S.mk x).toN := by
      rw [N.le_iff, S.subcomplex_toN, S.subcomplex_toN, Subfunctor.ofSection_le_iff,
        Subcomplex.mem_ofSimplex_obj_iff]
      exact ⟨f, rfl⟩
    apply yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply, SSet.yonedaEquiv_symm_map,
      Equiv.symm_apply_apply, ← s.w (homOfLE h)]
    dsimp
    simp only [← Category.assoc]; congr 1; simp only [Category.assoc]
    rw [← cancel_mono (Subcomplex.ι _)]
    apply yonedaEquiv.injective
    dsimp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.toOfSimplex_ι,
      yonedaEquiv_map_comp, Equiv.apply_symm_apply, S.map_toNπ]

@[simp]
lemma desc_app_apply {n : ℕ} (x : X _⦋n⦌) :
    (desc s).app _ x = descApp _ x := rfl

@[reassoc (attr := simp)]
def fac (x : X.N) : (Subcomplex.ofSimplex x.1.2).ι ≫ desc s = s.ι.app x := by
  rw [← cancel_epi (Subcomplex.toOfSimplex _),
    Subcomplex.toOfSimplex_ι_assoc, yonedaEquiv_symm_comp, desc_app_apply,
    descApp_apply']
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Subcomplex.yonedaEquiv_toOfSimplex]

end isColimitCoconeN

noncomputable def isColimitCoconeN : IsColimit X.coconeN where
  desc := isColimitCoconeN.desc
  fac := isColimitCoconeN.fac
  uniq s m hm := isColimitCoconeN.hom_ext (by aesop)

variable {X} {Y : SSet.{u}} (f : X ⟶ Y)

@[simps -isSimp coe]
noncomputable def mapN : X.N →o Y.N where
  toFun x := (S.map f x.toS).toN
  monotone' x x' h := by
    simp only [N.le_iff, S.subcomplex_toN, Subfunctor.ofSection_le_iff, S.map_dim,
      S.map_simplex, mem_ofSimplex_obj_iff] at h ⊢
    obtain ⟨g, hg⟩ := h
    exact ⟨g, by simp only [← hg, FunctorToTypes.naturality]⟩

@[simp]
lemma mapN_toN (x : X.S) :
    mapN f x.toN = (S.map f x).toN := by
  simp only [mapN_coe]
  simp [N.eq_iff]

lemma toS_mapN_of_nonDegenerate (x : X.N) (hx : f.app _ x.simplex ∈ Y.nonDegenerate _) :
    (mapN f x).toS = S.map f x.toS := by
  conv_lhs => rw [← x.toS_toN, mapN_toN]
  rw [S.toN_of_nonDegenerate _ hx]
  rfl

lemma toS_mapN_of_isIso (x : X.N) [IsIso f] :
    (mapN f x).toS = S.map f x.toS :=
  toS_mapN_of_nonDegenerate _ _
    (by simpa only [nonDegenerate_iff_of_isIso] using x.nonDegenerate)

lemma toS_mapN_of_mono (x : X.N) [Mono f] :
    (mapN f x).toS = S.map f x.toS :=
  toS_mapN_of_nonDegenerate _ _
    (by simpa only [nonDegenerate_iff_of_mono] using x.nonDegenerate)

@[simp]
lemma mapN_id : mapN (𝟙 X) = OrderHom.id := by
  ext x
  obtain ⟨x, rfl⟩ := x.toN_surjective
  simp

lemma mapN_mapN {Z : SSet.{u}} (g : Y ⟶ Z) (x : X.N) :
    mapN g (mapN f x) = mapN (f ≫ g) x := by
  obtain ⟨x, rfl⟩ := x.toN_surjective
  simp [S.map_map]

@[simp]
lemma subcomplex_mapN (x : X.N) : (mapN f x).subcomplex = Subcomplex.image x.subcomplex f := by
  simp [mapN]

namespace N

attribute [local simp] mapN_mapN in
@[simps]
noncomputable def functor : SSet.{u} ⥤ PartOrd.{u} where
  obj X := .of X.N
  map f := PartOrd.ofHom (mapN f)

end N

lemma N.mapN_ι_simplex_mem_obj {A : X.Subcomplex} (x : A.toSSet.N) :
    (mapN A.ι x).simplex ∈ A.obj _ := by
  rw [toS_mapN_of_mono]
  simp

@[simp]
lemma N.toSubcomplex_mapN_ι {A : X.Subcomplex} (x : A.toSSet.N) :
    (mapN A.ι x).toSubcomplex x.mapN_ι_simplex_mem_obj = x := by
  rw [N.ext_iff]
  apply S.map_injective_of_mono A.ι
  rw [toS_toSubcomplex, S.map_toSubcomplex, toS_mapN_of_mono A.ι]

@[simp]
lemma N.mapN_ι_toSubcomplex (x : X.N) {A : X.Subcomplex} (hx : x.simplex ∈ A.obj _) :
    mapN A.ι (x.toSubcomplex hx) = x := by
  rw [ext_iff, toS_mapN_of_mono, toS_toSubcomplex, S.map_ι_toSubcomplex]

lemma N.mapN_injective_of_mono [Mono f] :
    Function.Injective (mapN f) := by
  intro s t h
  rw [N.ext_iff] at h ⊢
  exact S.map_injective_of_mono f (by simpa only [toS_mapN_of_mono] using h)

instance [X.IsFinite] : Finite X.N :=
  Finite.of_surjective
    (fun (x : (Σ (n : ℕ), X.nonDegenerate n)) ↦ N.mk _ x.2.2) (by
      intro x
      obtain ⟨n, x, rfl⟩ := x.mk_surjective
      exact ⟨⟨n, x⟩, rfl⟩)

variable (X) in
lemma isFinite_iff_isFinite_n :
    X.IsFinite ↔ Finite X.N :=
  ⟨fun _ ↦ inferInstance, fun _ ↦
    ⟨Finite.of_surjective (fun (x : X.N) ↦ ⟨_, ⟨x.simplex, x.nonDegenerate⟩⟩)
      (fun ⟨_, x⟩ ↦ ⟨N.mk _ x.2, rfl⟩)⟩⟩

lemma N.dim_le_of_toS_le {x : X.N} {y : X.S} (h : x.toS ≤ y) : x.dim ≤ y.dim := by
  refine (N.le_of_le ?_).trans y.dim_toN_le
  rw [le_iff_toS_le_toS]
  exact h.trans (y.self_le_toS_toN)

lemma isFinite_iSup_iff {ι : Type*} [Finite ι] (A : ι → X.Subcomplex) :
    IsFinite (⨆ i, A i :) ↔ ∀ i, IsFinite (A i) := by
  refine ⟨fun _ i ↦ isFinite_of_mono (Subcomplex.homOfLE (le_iSup A i)), fun _ ↦ ?_⟩
  rw [isFinite_iff_isFinite_n]
  let f : (Σ (i : ι), (A i).toSSet.N) → (⨆ i, A i :).toSSet.N :=
    fun ⟨i, s⟩ ↦ N.mk' (S.map (Subcomplex.homOfLE (le_iSup A i)) s.toS) (by
      have := s.nonDegenerate
      rwa [Subcomplex.mem_nonDegenerate_iff] at this ⊢)
  refine Finite.of_surjective f (fun s ↦ ?_)
  obtain ⟨n, ⟨⟨s, hs⟩, hs'⟩, rfl⟩ := s.mk_surjective
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hs
  obtain ⟨i, hi⟩ := hs
  rw [Subcomplex.mem_nonDegenerate_iff] at hs'
  exact ⟨⟨i, N.mk ⟨s, hi⟩ (by rwa [Subcomplex.mem_nonDegenerate_iff])⟩, rfl⟩

end SSet
