import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Limits.Lattice
import TopCatModelCategory.SSet.Degenerate
import TopCatModelCategory.SSet.Evaluation
import TopCatModelCategory.SSet.Monomorphisms
import TopCatModelCategory.SSet.NonDegenerateSimplices
import TopCatModelCategory.ColimitsType

open CategoryTheory Simplicial HomotopicalAlgebra Limits Opposite

namespace SSet

lemma mono_of_nonDegenerate' {X : SSet.{u}} {d d' : ℕ} (x : X _⦋d⦌)
    (f : ⦋d'⦌ ⟶ ⦋d⦌)
    (h : X.map f.op x ∈ X.nonDegenerate d') : Mono f := by
  have := isIso_of_nonDegenerate _ ⟨_, h⟩ (factorThruImage f)
    (X.map (image.ι f).op x) (by
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, image.fac])
  rw [← image.fac f]
  infer_instance

variable (X : SSet.{u})

variable {X} {Y : SSet.{u}} (i : X ⟶ Y)

namespace relativeCellComplexOfMono

variable (d : ℕ)

def ι [Mono i] : Type u :=
  { y : Y.nonDegenerate d // y.1 ∉ (Subcomplex.range i).obj _ }

variable [Mono i]

noncomputable def A : SSet.{u} := ∐ (fun (_ : ι i d) ↦ boundary d)

noncomputable def B : SSet.{u} := ∐ (fun (_ : ι i d) ↦ Δ[d])

variable {i d}

noncomputable def ιA (x : ι i d) : (boundary d : SSet) ⟶ A i d :=
  Limits.Sigma.ι (fun _ ↦ _) x

noncomputable def ιB (x : ι i d) : Δ[d] ⟶ B i d :=
  Limits.Sigma.ι (fun _ ↦ _) x

lemma ιA_jointly_surjective {n : ℕ} (a : (A i d) _⦋n⦌) :
    ∃ (x : ι i d) (a' : (∂Δ[d] : SSet) _⦋n⦌), (ιA x).app _ a' = a :=
  Types.jointly_surjective_of_isColimit_cofan
    (isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj (op ⦋n⦌)) _ _
    (coproductIsCoproduct _)) a

lemma ιB_jointly_surjective {n : ℕ} (b : (B i d) _⦋n⦌) :
    ∃ (x : ι i d) (b' : Δ[d] _⦋n⦌), (ιB x).app _ b' = b :=
  Types.jointly_surjective_of_isColimit_cofan
    (isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj (op ⦋n⦌)) _ _
    (coproductIsCoproduct _)) b

variable (i d) in
noncomputable def m : A i d ⟶ B i d := Limits.Sigma.map (fun _ ↦ (boundary d).ι)

instance : Mono (m i d) := by
  dsimp [m]
  infer_instance

@[reassoc (attr := simp)]
lemma ιA_m (x : ι i d) : ιA x ≫ m i d = (boundary d).ι ≫ ιB x := by
  simp [m, ιA, ιB]

lemma mem_skeletonOfMono (x : ι i d) {d' : ℕ} (h : d < d') :
    x.1.1 ∈ (skeletonOfMono i d').obj _ := by
  simp only [skeletonOfMono, OrderHom.coe_mk, Subfunctor.max_obj, Set.mem_union]
  exact Or.inr (Y.mem_skeleton _ h)

def β (x : ι i d) : Δ[d] ⟶ skeletonOfMono i (d + 1) :=
  yonedaEquiv.symm ⟨x.1.1, mem_skeletonOfMono x (by simp)⟩

variable (i d) in
noncomputable def b : B i d ⟶ skeletonOfMono i (d + 1) := Sigma.desc β

@[reassoc (attr := simp)]
lemma ιB_b (x : ι i d) : ιB x ≫ b i d = β x := by simp [ιB, b]

lemma preimage_skeletonOfMono_eq (x : ι i d) :
    (skeletonOfMono i d).preimage (yonedaEquiv.symm x.1.1) = ∂Δ[d] := by
  rw [stdSimplex.eq_boundary_iff]
  constructor
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro n ⟨y, hy₁⟩ hy₂
    have : n < d := dim_lt_of_nondegenerate (X := ∂Δ[d])
      (⟨⟨y, hy₂⟩, by rwa [Subcomplex.mem_nonDegenerate_iff]⟩) d
    simp [skeletonOfMono_obj_eq_top i this]
  · intro h
    have := h.symm.le _ (show stdSimplex.objEquiv.symm (𝟙 ⦋d⦌)  ∈ _ by simp)
    simp only [Subfunctor.range_obj, Subcomplex.preimage_obj, Set.mem_preimage] at this
    change Y.map (𝟙 _) x.1.1 ∈ (skeletonOfMono i d).obj _ at this
    simp only [Subfunctor.range_obj, FunctorToTypes.map_id_apply,
      mem_skeletonOfMono_obj_iff_of_nonDegenerate, Set.mem_range, lt_self_iff_false,
      or_false] at this
    exact x.2 this

def τ (x : ι i d) : (∂Δ[d] : SSet) ⟶ skeletonOfMono i d :=
  Subcomplex.liftFromPreimage (∂Δ[d].ι ≫ yonedaEquiv.symm x.1.1) (by
    rw [Subcomplex.preimage_preimage, preimage_skeletonOfMono_eq,
      Subcomplex.preimage_ι])

@[simp]
lemma τ_app_coe (x : ι i d) {n : ℕ} (a : (∂Δ[d] : SSet) _⦋n⦌) :
    ((τ x).app _ a).1 = (β x).app _ a.1 := rfl

variable (i d) in
noncomputable def t : A i d ⟶ skeletonOfMono i d := Sigma.desc τ

@[reassoc (attr := simp)]
lemma ιA_t (x : ι i d) : ιA x ≫ t i d = τ x := by simp [ιA, t]

variable (i d) in
def r : (skeletonOfMono i d : SSet) ⟶ skeletonOfMono i (d + 1) :=
  Subcomplex.homOfLE ((skeletonOfMono i).monotone (by simp))

variable (i d) in
instance mono_r : Mono (r i d) := by dsimp [r]; infer_instance

@[reassoc]
lemma τ_r (x : ι i d) : τ x ≫ r i d = ∂Δ[d].ι ≫ β x := rfl

@[simp]
lemma r_app_coe {n : ℕ} (y : (skeletonOfMono i d : SSet) _⦋n⦌) :
    ((r i d).app _ y).1 = y.1 := rfl

variable (i d)

@[reassoc]
lemma w : t i d ≫ r i d = m i d ≫ b i d :=
  Sigma.hom_ext _ _ (fun x ↦ by
    change ιA x ≫ t i d ≫ r i d = ιA x ≫ m i d ≫ b i d
    simp [τ_r])

lemma sup_range_r_range_b :
    Subcomplex.range (r i d) ⊔ Subcomplex.range (b i d) = ⊤ := by
  rw [← top_le_iff]
  rintro n ⟨x, hx⟩ _
  simp only [skeletonOfMono_succ, Subfunctor.range_obj, Set.mem_range, not_exists,
    Subfunctor.max_obj, Subfunctor.iSup_obj, Subcomplex.iSup_obj, Set.iUnion_coe_set,
    Set.mem_union, Set.mem_iUnion, exists_prop] at hx
  simp only [Subfunctor.toFunctor_obj, Subfunctor.max_obj, Subfunctor.range_obj, Set.mem_union,
    Set.mem_range, Subtype.exists]
  obtain hx | ⟨y, hy₁, hy₂, ⟨f⟩, rfl⟩  := hx
  · exact Or.inl ⟨x, hx, rfl⟩
  · refine Or.inr ⟨(ιB ⟨⟨y, hy₁⟩, by simpa⟩).app _
      (stdSimplex.objEquiv.symm f), ?_⟩
    rw [← FunctorToTypes.comp, ιB_b]
    rfl

lemma range_r_app_union_range_b_app (n : SimplexCategoryᵒᵖ) :
    Set.range ((r i d).app n) ∪
      Set.range ((b i d).app n) = Set.univ :=
  congr_fun (congr_arg Subfunctor.obj (sup_range_r_range_b i d)) n

lemma isPullback : IsPullback (t i d) (m i d) (r i d) (b i d) where
  w := w i d
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨n⟩ ↦ by
    refine (isLimitMapConePullbackConeEquiv _ _).2
      (IsPullback.isLimit ?_)
    induction n using SimplexCategory.rec with | _ n
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨?_, ?_, ?_⟩
    · exact (congr_app (w i d) (op ⦋n⦌))
    · intro a₁ a₂ ⟨ht, hm⟩
      have : Mono (m i d) := inferInstance
      rw [NatTrans.mono_iff_mono_app] at this
      simp only [mono_iff_injective] at this
      exact this _ hm
    · intro y b h
      obtain ⟨x, b, rfl⟩ := ιB_jointly_surjective b
      have hb : b ∈ ∂Δ[d].obj _ := by
        obtain ⟨y, hy⟩ := y
        rw [← preimage_skeletonOfMono_eq x]
        rw [Subtype.ext_iff] at h
        dsimp at h
        subst h
        rwa [← FunctorToTypes.comp, ιB_b] at hy
      refine ⟨(ιA x).app _ ⟨b, hb⟩, ?_, ?_⟩
      · rw [Subtype.ext_iff] at h
        dsimp at h
        rw [← FunctorToTypes.comp, ιA_t]
        rw [← FunctorToTypes.comp, ιB_b] at h
        ext
        exact h.symm
      · rw [← FunctorToTypes.comp, ιA_m, comp_app, types_comp_apply,
          Subfunctor.ι_app])⟩


variable {i d} in
lemma exists_epi {n : ℕ} (y : (B i d) _⦋n⦌)
    (hy : y ∉ Set.range ((m i d).app (op ⦋n⦌))) :
    ∃ (x : ι i d) (f : ⦋n⦌ ⟶ ⦋d⦌) (_ : Epi f),
    (ιB x).app (op ⦋n⦌) (stdSimplex.objEquiv.symm f) = y := by
  obtain ⟨x, s, rfl⟩ := ιB_jointly_surjective y
  have hs : s ∉ ∂Δ[d].obj _ := fun hs ↦ hy (⟨(ιA x).app _ ⟨s, hs⟩, by
    rw [← FunctorToTypes.comp, ιA_m, comp_app, types_comp_apply, Subfunctor.ι_app]⟩)
  refine ⟨x, stdSimplex.objEquiv (m := op ⦋n⦌) s,
    by simpa [SimplexCategory.epi_iff_surjective, boundary] using hs,
    by simp⟩

lemma isPushout : IsPushout (t i d) (m i d) (r i d) (b i d) where
  w := w i d
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨n⟩ ↦ by
    induction n using SimplexCategory.rec with | _ n
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2
      (IsPushout.isColimit ?_)
    have := mono_r i d
    refine Limits.Types.isPushout_of_isPullback_of_mono' ?_ ?_ ?_
    · exact (isPullback i d).map ((evaluation _ _).obj (op ⦋n⦌))
    · exact range_r_app_union_range_b_app _ _ _
    · dsimp
      intro y₁ y₂ hy₁ hy₂ h
      obtain ⟨x₁, f₁, _, rfl⟩ := exists_epi y₁ hy₁
      obtain ⟨x₂, f₂, _, rfl⟩ := exists_epi y₂ hy₂
      have h' : Y.map f₁.op x₁.1.1 = Y.map f₂.op x₂.1.1 := by
        rwa [← FunctorToTypes.comp, ← FunctorToTypes.comp, ιB_b, ιB_b,
          Subtype.ext_iff] at h
      obtain rfl : x₁ = x₂ := by
        rw [Subtype.ext_iff]
        exact Y.unique_nonDegenerate_simplex _ f₁ x₁.1 rfl f₂ x₂.1 h'
      obtain rfl : f₁ = f₂ :=
        Y.unique_nonDegenerate_map _ f₁ x₁.1 rfl f₂ x₁.1 h'
      rfl)⟩

end relativeCellComplexOfMono

open relativeCellComplexOfMono in
noncomputable def relativeCellComplexOfMono [Mono i] :
    RelativeCellComplex.{u} (basicCell := fun (n : ℕ) (_ : Unit) ↦ (boundary n).ι) i where
  F := (skeletonOfMono i).monotone.functor ⋙ Subcomplex.toPresheafFunctor
  isoBot := Subcomplex.isoOfEq (by simp) ≪≫ (asIso (toRangeSubcomplex i)).symm
  incl :=
    { app _ := Subcomplex.ι _
      naturality _ _ _ := rfl }
  isColimit := IsColimit.ofIsoColimit
      (isColimitOfPreserves Subcomplex.toPresheafFunctor
        ((CompleteLattice.colimitCocone
        ((skeletonOfMono i).monotone.functor)).isColimit))
          (Cocones.ext
            ((Subcomplex.isoOfEq (iSup_skeletonOfMono i)) ≪≫ Subcomplex.topIso Y)
        (fun _ ↦ by rfl))
  attachCells d hd :=
    { ι := ι i d
      π _ := ⟨⟩
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := m i d
      hm := ιA_m
      g₁ := t i d
      g₂ := b i d
      isPushout := isPushout i d }

open relativeCellComplexOfMono in
lemma relativeCellComplexOfMono_attachCells_cell [Mono i] {d : ℕ} (s : ι i d) :
    ((relativeCellComplexOfMono i).attachCells d (by simp)).cell s = β s :=
  Sigma.ι_desc _ _

variable (X) in
noncomputable def relativeCellComplex :
    RelativeCellComplex.{u} (basicCell := fun (n : ℕ) (_ : Unit) ↦ (boundary n).ι)
      (Subcomplex.ι ⊥ : _ ⟶ X) :=
  relativeCellComplexOfMono _

variable (X) in
@[simps]
def relativeCellComplexCellsEquiv :
    (relativeCellComplex X).Cells ≃ X.N where
  toFun c := N.mk _ c.k.1.2
  invFun s :=
    { j := s.dim
      hj := by simp
      k := ⟨⟨_, s.nonDegenerate⟩, by simp ⟩ }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma relativeCellComplexι_eq (s : (relativeCellComplex X).Cells) :
    s.ι = yonedaEquiv.symm s.k.1.1 := by
  dsimp only [relativeCellComplex, RelativeCellComplex.Cells.ι] at s ⊢
  rw [relativeCellComplexOfMono_attachCells_cell]
  apply yonedaEquiv_symm_comp

namespace modelCategoryQuillen

open MorphismProperty

noncomputable def transfiniteCompositionOfMono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    (coproducts.{u} I).pushouts.TransfiniteCompositionOfShape ℕ i where
  toTransfiniteCompositionOfShape :=
    (relativeCellComplexOfMono i).toTransfiniteCompositionOfShape
  map_mem d hd := by
    apply pushouts_monotone _ _
      ((relativeCellComplexOfMono i).attachCells d hd).pushouts_coproducts
    apply coproducts_monotone
    rintro _ _ _ ⟨⟩
    exact boundary_ι_mem_I d

lemma transfiniteCompositions_pushouts_coproducts :
    transfiniteCompositions.{u} (coproducts.{u} I).pushouts = monomorphisms SSet.{u} := by
  apply le_antisymm
  · rw [transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact I_le_monomorphisms
  · intro _ _ i (_ : Mono i)
    apply transfiniteCompositionsOfShape_le_transfiniteCompositions _ (ULift ℕ)
    exact ⟨(transfiniteCompositionOfMono i).ofOrderIso (orderIsoULift.{u} ℕ).symm⟩

lemma I_rlp_eq_monomorphisms_rlp : I.{u}.rlp = (monomorphisms SSet.{u}).rlp := by
  apply le_antisymm
  · simp only [← transfiniteCompositions_pushouts_coproducts,
      rlp_transfiniteCompositions, rlp_pushouts, rlp_coproducts, le_refl]
  · exact MorphismProperty.antitone_rlp I_le_monomorphisms

end modelCategoryQuillen

end SSet
