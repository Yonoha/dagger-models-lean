import AmalgamReductionEncoding

/-! Strong local diamond on the literal contextual relation defining the actual quotient. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation

universe u

namespace DaggerAmalgamReduction

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)
variable {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}

theorem lift_encoded_refl {p : Path B B' b b' q a z} {l : List (Edge B B' q)}
    (h : Relation.ReflGen (ReverseEncodedRed B B' q) (encode B B' b b' p) l) :
    ∃ p' : Path B B' b b' q a z, Relation.ReflGen (Red B B' b b' q a z) p p' ∧
      encode B B' b b' p' = l := by
  cases h with
  | refl => exact ⟨p, .refl, rfl⟩
  | single h =>
    obtain ⟨p', hh, he⟩ := lift_encoded B B' b b' h p rfl
    exact ⟨p', .single hh, he⟩

/-- In fact both branches need at most one actual contextual step. -/
theorem strong_diamond_refl {p p₁ p₂ : Path B B' b b' q a z}
    (h₁ : Red B B' b b' q a z p p₁) (h₂ : Red B B' b b' q a z p p₂) :
    ∃ d, Relation.ReflGen (Red B B' b b' q a z) p₁ d ∧
      Relation.ReflGen (Red B B' b b' q a z) p₂ d := by
  obtain ⟨l, hl₁, hl₂⟩ := reverse_encoded_diamond B B' q
    (red_encode B B' b b' h₁) (red_encode B B' b b' h₂)
  obtain ⟨d₁, hd₁, he₁⟩ := lift_encoded_refl B B' b b' hl₁
  obtain ⟨d₂, hd₂, he₂⟩ := lift_encoded_refl B B' b b' hl₂
  have hd : d₁ = d₂ := encode_injective B B' b b' (he₁.trans he₂.symm)
  exact ⟨d₁, hd₁, hd ▸ hd₂⟩

/-- The exact premise of pinned Relation.church_rosser, with no caller hypotheses. -/
theorem strong_diamond (q : SimplexCategoryᵒᵖ) (a z : Objects B B' b b') :
    ∀ p p₁ p₂ : Path B B' b b' q a z,
      Red B B' b b' q a z p p₁ → Red B B' b b' q a z p p₂ →
        ∃ d, Relation.ReflGen (Red B B' b b' q a z) p₁ d ∧
          Relation.ReflTransGen (Red B B' b b' q a z) p₂ d := by
  intro p p₁ p₂ h₁ h₂
  obtain ⟨d, hd₁, hd₂⟩ := strong_diamond_refl B B' b b' h₁ h₂
  exact ⟨d, hd₁, hd₂.to_reflTransGen⟩

/-- Original factor middle endpoints follow from the actual embedding, not a premise. -/
theorem same_color_middle (c : Bool) (x y : (factor B B' c).Obj)
    (h : label B B' b b' c x = label B B' b b' c y) : x = y :=
  label_injective B B' b b' c h

/-- Every original simplex operator preserves the SAME one-step relation. -/
theorem red_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a z : Objects B B' b b'} {p p' : Path B B' b b' q a z}
    (h : Red B B' b b' q a z p p') :
    Red B B' b b' q' a z (SimplicialColimitsFree.Paths.map _ α p)
      (SimplicialColimitsFree.Paths.map _ α p') := by
  rcases h with ⟨s, t, l, r, r', v, h⟩
  change Red B B' b b' q' a z
    (SimplicialColimitsFree.Paths.map _ α (l.comp (r.comp v)))
    (SimplicialColimitsFree.Paths.map _ α (l.comp (r'.comp v)))
  simp only [SimplicialColimitsFree.Paths.map_pathComp]
  have hh : SimplicialCat.HomQuotient.degreeRel (relations B B' b b') q'
      (SimplicialColimitsFree.Paths.map _ α r) (SimplicialColimitsFree.Paths.map _ α r') :=
    relations_map B B' b b' α h
  exact @HomRel.CompClosure.intro (SimplicialEnrichment.At (free B B' b b').Obj q') _
    (SimplicialCat.HomQuotient.degreeRel (relations B B' b b') q') a z s t
    (SimplicialColimitsFree.Paths.map (graph B B' b b') α l)
    (SimplicialColimitsFree.Paths.map (graph B B' b b') α r)
    (SimplicialColimitsFree.Paths.map (graph B B' b b') α r')
    (SimplicialColimitsFree.Paths.map (graph B B' b b') α v) hh

end DaggerAmalgamReduction
