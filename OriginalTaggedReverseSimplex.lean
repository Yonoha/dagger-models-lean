import DaggerModels.ReverseSimplex

/-!
# The tagged reversal simplex category

This is the pair normal form of `pointset.def.tagged` and
`pointset.lem.normal-forms`. The tag is retained even in degree zero.
The functor to `ReverseSimplex` records the underlying set map.
-/

open CategoryTheory

namespace DaggerModels.OriginalTaggedReverseSimplex

/-- Objects are the nonempty finite ordinals. -/
structure TaggedReverseSimplex where
  len : ℕ

namespace TaggedReverseSimplex

/-- `⟨α, true⟩` represents the normal form `ρ̃_n α`. -/
structure Hom (m n : TaggedReverseSimplex) where
  base : SimplexCategory.mk m.len ⟶ SimplexCategory.mk n.len
  tag : Bool

@[ext]
theorem Hom.ext {m n : TaggedReverseSimplex} {f g : Hom m n}
    (hbase : f.base = g.base) (htag : f.tag = g.tag) : f = g := by
  cases f
  cases g
  cases hbase
  cases htag
  rfl

/-- The multiplication `(β,h) ∘ (α,g) = (rev^g β ∘ α,hg)`. -/
def Hom.comp {m n p : TaggedReverseSimplex} (f : Hom m n) (g : Hom n p) : Hom m p :=
  ⟨f.base ≫ (if f.tag then SimplexCategory.rev.map g.base else g.base),
    xor f.tag g.tag⟩

instance taggedSmallCategory : SmallCategory TaggedReverseSimplex where
  Hom := Hom
  id n := ⟨𝟙 _, false⟩
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext <;> simp [Hom.comp]
  comp_id f := by
    cases f with
    | mk α tag =>
      cases tag <;> apply Hom.ext <;>
        simp [Hom.comp]
  assoc f g h := by
    cases f with
    | mk α a =>
      cases g with
      | mk β b =>
        cases h with
        | mk γ c =>
          cases a <;> cases b <;> cases c <;>
            apply Hom.ext <;>
            simp [Hom.comp, Category.assoc, Functor.map_comp,
              SimplexCategory.rev_map_rev_map]

/-- The ordinary simplex category has the false tag. -/
def simplexInclusion : SimplexCategory ⥤ TaggedReverseSimplex where
  obj n := ⟨n.len⟩
  map f := ⟨f, false⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The tagged reversal remains nontrivial at `[0]`. -/
def taggedReversal (n : TaggedReverseSimplex) : n ⟶ n := ⟨𝟙 _, true⟩

@[simp]
theorem taggedReversal_sq (n : TaggedReverseSimplex) :
    taggedReversal n ≫ taggedReversal n = 𝟙 n := by
  change Hom.comp (taggedReversal n) (taggedReversal n) =
    (⟨𝟙 _, false⟩ : Hom n n)
  apply Hom.ext <;> simp [taggedReversal, Hom.comp]

theorem taggedReversal_cross {m n : SimplexCategory} (f : m ⟶ n) :
    simplexInclusion.map f ≫ taggedReversal ⟨n.len⟩ =
      taggedReversal ⟨m.len⟩ ≫ simplexInclusion.map (SimplexCategory.rev.map f) := by
  change Hom.comp (simplexInclusion.map f) (taggedReversal ⟨n.len⟩) =
    Hom.comp (taggedReversal ⟨m.len⟩)
      (simplexInclusion.map (SimplexCategory.rev.map f))
  apply Hom.ext <;> simp [taggedReversal, simplexInclusion, Hom.comp]

theorem taggedReversal_zero_ne_id :
    taggedReversal ⟨0⟩ ≠ 𝟙 (TaggedReverseSimplex.mk 0) := by
  intro h
  have ht := congrArg (fun f : Hom ⟨0⟩ ⟨0⟩ ↦ f.tag) h
  cases ht

/-- The literal monotone or antitone function represented by a tagged pair. -/
def qMap {m n : TaggedReverseSimplex} (f : m ⟶ n) :
    ReverseSimplex.mk m.len ⟶ ReverseSimplex.mk n.len := by
  refine ⟨fun i ↦ if f.tag then (f.base.toOrderHom i).rev else f.base.toOrderHom i,
    ?_⟩
  cases h : f.tag with
  | false =>
    exact Or.inl (by simpa [h] using f.base.toOrderHom.monotone)
  | true =>
    exact Or.inr (by
      intro i j hij
      simpa [h] using f.base.toOrderHom.monotone hij)

theorem qMap_comp {m n p : TaggedReverseSimplex} (f : m ⟶ n) (g : n ⟶ p) :
    qMap (f ≫ g) = qMap f ≫ qMap g := by
  change qMap (Hom.comp f g) = ReverseSimplex.Hom.comp (qMap f) (qMap g)
  apply ReverseSimplex.Hom.ext
  intro i
  cases hf : f.tag <;> cases hg : g.tag <;>
    simp [qMap, Hom.comp, ReverseSimplex.Hom.comp, hf, hg,
      SimplexCategory.rev]
  all_goals rfl

/-- Forget the tag by evaluating the underlying finite-ordinal function. -/
def qTag : TaggedReverseSimplex ⥤ ReverseSimplex where
  obj n := ⟨n.len⟩
  map f := qMap f
  map_id n := by
    apply ReverseSimplex.Hom.ext
    intro i
    rfl
  map_comp f g := qMap_comp f g

theorem qTag_inclusion : simplexInclusion ⋙ qTag = ReverseSimplex.inclusion := by
  apply CategoryTheory.Functor.ext
  · intro m n f
    apply ReverseSimplex.Hom.ext
    intro i
    rfl
  · intro n
    rfl

theorem qTag_taggedReversal (n : TaggedReverseSimplex) :
    qTag.map (taggedReversal n) = ReverseSimplex.reversal ⟨n.len⟩ := by
  apply ReverseSimplex.Hom.ext
  intro i
  rfl

theorem qTag_identifies_zero :
    qTag.map (taggedReversal ⟨0⟩) = qTag.map (𝟙 (TaggedReverseSimplex.mk 0)) := by
  rw [qTag_taggedReversal, qTag.map_id]
  exact ReverseSimplex.reversal_zero

theorem qMap_surjective (m n : TaggedReverseSimplex) :
    Function.Surjective (qMap : (m ⟶ n) →
      (ReverseSimplex.mk m.len ⟶ ReverseSimplex.mk n.len)) := by
  intro f
  rcases f.monotone_or_antitone with hm | ha
  · let α : SimplexCategory.mk m.len ⟶ SimplexCategory.mk n.len :=
      SimplexCategory.Hom.mk ⟨f.toFun, hm⟩
    refine ⟨⟨α, false⟩, ?_⟩
    apply ReverseSimplex.Hom.ext
    intro i
    rfl
  · let α : SimplexCategory.mk m.len ⟶ SimplexCategory.mk n.len :=
      SimplexCategory.Hom.mk ⟨fun i ↦ (f.toFun i).rev, by
        intro i j hij
        exact (Fin.rev_le_rev).2 (ha hij)⟩
    refine ⟨⟨α, true⟩, ?_⟩
    apply ReverseSimplex.Hom.ext
    intro i
    simp [qMap, α]

/-- Exact equality test for the underlying functions, with both tags visible. -/
theorem qMap_eq_iff {m n : TaggedReverseSimplex} (f g : m ⟶ n) :
    qMap f = qMap g ↔
      ∀ i : Fin (m.len + 1),
        (if f.tag then (f.base.toOrderHom i).rev else f.base.toOrderHom i) =
          (if g.tag then (g.base.toOrderHom i).rev else g.base.toOrderHom i) := by
  constructor
  · intro h i
    exact congrArg (fun k : ReverseSimplex.mk m.len ⟶ ReverseSimplex.mk n.len ↦
      k.toFun i) h
  · intro h
    apply ReverseSimplex.Hom.ext
    exact h

/-- Opposite-tag equality is exactly the pair `c_k` and `ρ̃_n c_(n-k)`. -/
theorem qMap_false_eq_true_iff {m n : TaggedReverseSimplex}
    (α β : SimplexCategory.mk m.len ⟶ SimplexCategory.mk n.len) :
    qMap (⟨α, false⟩ : m ⟶ n) = qMap (⟨β, true⟩ : m ⟶ n) ↔
      ∃ k : Fin (n.len + 1),
        (∀ i, α.toOrderHom i = k) ∧ (∀ i, β.toOrderHom i = k.rev) := by
  constructor
  · intro h
    have heq (i : Fin (m.len + 1)) :
        α.toOrderHom i = (β.toOrderHom i).rev := by
      exact congrArg (fun t : ReverseSimplex.mk m.len ⟶
        ReverseSimplex.mk n.len ↦ t.toFun i) h
    have ha : Antitone (fun i : Fin (m.len + 1) ↦ α.toOrderHom i) := by
      intro i j hij
      calc
        α.toOrderHom j = (β.toOrderHom j).rev := heq j
        _ ≤ (β.toOrderHom i).rev := by
          simpa using β.toOrderHom.monotone hij
        _ = α.toOrderHom i := (heq i).symm
    have hc := (ReverseSimplex.monotone_antitone_iff_constant
      (m := ReverseSimplex.mk m.len) (n := ReverseSimplex.mk n.len)
      (fun i : Fin (m.len + 1) ↦ α.toOrderHom i)).mp
        ⟨α.toOrderHom.monotone, ha⟩
    refine ⟨α.toOrderHom 0, (fun i ↦ hc i 0), ?_⟩
    intro i
    have hi := heq i
    rw [hc i 0] at hi
    calc
      β.toOrderHom i = ((β.toOrderHom i).rev).rev := (Fin.rev_rev _).symm
      _ = (α.toOrderHom 0).rev := (congrArg Fin.rev hi).symm
  · rintro ⟨k, hα, hβ⟩
    apply ReverseSimplex.Hom.ext
    intro i
    change α.toOrderHom i = (β.toOrderHom i).rev
    rw [hα i, hβ i, Fin.rev_rev]

end TaggedReverseSimplex
end DaggerModels.OriginalTaggedReverseSimplex
