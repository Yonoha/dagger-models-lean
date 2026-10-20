import OriginalTaggedReverseSimplex

/-!
# The degree-zero relation for the tagged reversal category

The actual functor to `ReverseSimplex` identifies only opposite-tag constant
maps. A target functor that identifies the tagged reversal at degree zero
therefore respects every fiber of this functor on Hom sets.
-/

open CategoryTheory

namespace DaggerModels.OriginalTaggedReverseQuotient

open DaggerModels.OriginalTaggedReverseSimplex
open TaggedReverseSimplex

universe u v

variable {C : Type u} [Category.{v} C]

/-- Opposite tagged constants have equal images when the zero reversal acts trivially. -/
theorem map_opposite_constants_eq (H : TaggedReverseSimplex ⥤ C)
    (hzero : H.map (taggedReversal ⟨0⟩) = 𝟙 (H.obj ⟨0⟩))
    {m n : TaggedReverseSimplex}
    (α β : SimplexCategory.mk m.len ⟶ SimplexCategory.mk n.len)
    (h : qMap (⟨α, false⟩ : m ⟶ n) = qMap (⟨β, true⟩ : m ⟶ n)) :
    H.map (⟨α, false⟩ : m ⟶ n) = H.map (⟨β, true⟩ : m ⟶ n) := by
  obtain ⟨k, hα, hβ⟩ := (qMap_false_eq_true_iff α β).mp h
  let z : TaggedReverseSimplex := ⟨0⟩
  let drop : m ⟶ z := ⟨SimplexCategory.const _ _ 0, false⟩
  let pick : z ⟶ n := ⟨SimplexCategory.const _ _ k, false⟩
  have hfalse : (⟨α, false⟩ : m ⟶ n) = drop ≫ pick := by
    change (⟨α, false⟩ : Hom m n) = Hom.comp drop pick
    apply Hom.ext
    · apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      change α.toOrderHom i = k
      exact hα i
    · rfl
  have htrue : (⟨β, true⟩ : m ⟶ n) =
      drop ≫ (taggedReversal z ≫ pick) := by
    change (⟨β, true⟩ : Hom m n) =
      Hom.comp drop (Hom.comp (taggedReversal z) pick)
    apply Hom.ext
    · apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      change β.toOrderHom i = k.rev
      exact hβ i
    · rfl
  have hz : H.map (taggedReversal z) = 𝟙 (H.obj z) := by
    simpa [z] using hzero
  rw [hfalse, htrue, H.map_comp drop pick,
    H.map_comp drop (taggedReversal z ≫ pick),
    H.map_comp (taggedReversal z) pick, hz]
  simp

/-- The degree-zero relation kills exactly the kernel of the actual `qMap`. -/
theorem map_eq_of_qMap_eq (H : TaggedReverseSimplex ⥤ C)
    (hzero : H.map (taggedReversal ⟨0⟩) = 𝟙 (H.obj ⟨0⟩))
    {m n : TaggedReverseSimplex} (f g : m ⟶ n) (h : qMap f = qMap g) :
    H.map f = H.map g := by
  rcases f with ⟨α, a⟩
  rcases g with ⟨β, b⟩
  cases a <;> cases b
  · have hab : α = β := by
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      exact (qMap_eq_iff (⟨α, false⟩ : m ⟶ n) ⟨β, false⟩).mp h i
    cases hab
    rfl
  · exact map_opposite_constants_eq H hzero α β h
  · exact (map_opposite_constants_eq H hzero β α h.symm).symm
  · have hab : α = β := by
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      have hi := (qMap_eq_iff (⟨α, true⟩ : m ⟶ n) ⟨β, true⟩).mp h i
      simpa using congrArg Fin.rev hi
    cases hab
    rfl

/-- Choose a tagged representative of each actual monotone-or-antitone map. -/
private noncomputable def representative {m n : ReverseSimplex} (f : m ⟶ n) :
    TaggedReverseSimplex.mk m.len ⟶ TaggedReverseSimplex.mk n.len :=
  Classical.choose (qMap_surjective ⟨m.len⟩ ⟨n.len⟩ f)

private theorem representative_spec {m n : ReverseSimplex} (f : m ⟶ n) :
    qMap (representative f) = f :=
  Classical.choose_spec (qMap_surjective ⟨m.len⟩ ⟨n.len⟩ f)

/-- Descend a functor through the actual underlying-function functor. -/
noncomputable def factor (H : TaggedReverseSimplex ⥤ C)
    (hzero : H.map (taggedReversal ⟨0⟩) = 𝟙 (H.obj ⟨0⟩)) :
    ReverseSimplex ⥤ C where
  obj n := H.obj ⟨n.len⟩
  map f := H.map (representative f)
  map_id n := by
    have h : qMap (representative (𝟙 n)) =
        qMap (𝟙 (TaggedReverseSimplex.mk n.len)) := by
      rw [representative_spec]
      exact (qTag.map_id ⟨n.len⟩).symm
    exact (map_eq_of_qMap_eq H hzero _ _ h).trans (H.map_id ⟨n.len⟩)
  map_comp f g := by
    have h : qMap (representative (f ≫ g)) =
        qMap (representative f ≫ representative g) := by
      rw [representative_spec, qMap_comp, representative_spec, representative_spec]
    exact (map_eq_of_qMap_eq H hzero _ _ h).trans
      (H.map_comp (representative f) (representative g))

/-- The factor agrees with the original functor on every tagged object and Hom. -/
theorem factor_fac (H : TaggedReverseSimplex ⥤ C)
    (hzero : H.map (taggedReversal ⟨0⟩) = 𝟙 (H.obj ⟨0⟩)) :
    qTag ⋙ factor H hzero = H := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro m n f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    map_eq_of_qMap_eq H hzero _ _ (representative_spec (qMap f))

/-- A functor through `qTag` is uniquely determined by its tagged restriction. -/
theorem factor_unique (H : TaggedReverseSimplex ⥤ C)
    (hzero : H.map (taggedReversal ⟨0⟩) = 𝟙 (H.obj ⟨0⟩))
    (G : ReverseSimplex ⥤ C) (hG : qTag ⋙ G = H) :
    G = factor H hzero := by
  subst H
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change G.map f = G.map (qMap (representative f))
  rw [representative_spec]

end DaggerModels.OriginalTaggedReverseQuotient
