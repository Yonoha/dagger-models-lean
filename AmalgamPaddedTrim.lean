import AmalgamPaddedParse
import AmalgamPaddedInjection

/-! Removing only the two endpoint identity letters by the original relation.
Every encoded reduction is lifted back to the same actual dependent path. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem lift_encoded_finite {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) {l : List (Edge C B q)}
    (h : Relation.ReflTransGen (ReverseEncodedRed C B q) (encode C B x b p) l) :
    ∃ p' : Path C B x b q s t,
      Relation.ReflTransGen (Red C B x b q s t) p p' ∧ encode C B x b p' = l := by
  generalize he : encode C B x b p = l₀ at h
  induction h with
  | refl => exact ⟨p, .refl, he⟩
  | @tail l₁ l₂ h₁ h₂ ih =>
    obtain ⟨p₁, hr, hp⟩ := ih
    obtain ⟨p₂, hs, ht⟩ := lift_encoded C B x b h₂ p₁ hp
    exact ⟨p₂, hr.tail hs, ht⟩

def cutHead {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q)) : List (Edge C B q) := by
  classical
  exact match l with
    | [] => []
    | e :: l => if IsIdentity C B q e then l else e :: l

def cutTail {q : SimplexCategoryᵒᵖ} : List (Edge C B q) → List (Edge C B q) := by
  classical
  exact fun l ↦ match l with
    | [] => []
    | e :: [] => if IsIdentity C B q e then [] else [e]
    | e :: d :: l => e :: cutTail (d :: l)

def trimEndpoints {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q)) : List (Edge C B q) :=
  cutTail C B (cutHead C B l)

theorem cutHead_reduces {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q)) :
    Relation.ReflTransGen (ReverseEncodedRed C B q) l (cutHead C B l) := by
  classical
  cases l with
  | nil => exact .refl
  | cons e l =>
    by_cases hi : IsIdentity C B q e
    · simpa only [cutHead, if_pos hi] using
        Relation.ReflTransGen.single (ListRed.delete e l hi)
    · simp only [cutHead, if_neg hi]
      exact .refl

theorem cutTail_reduces {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q)) :
    Relation.ReflTransGen (ReverseEncodedRed C B q) l (cutTail C B l) := by
  classical
  induction l with
  | nil => exact .refl
  | cons e l ih =>
    cases l with
    | nil =>
      by_cases hi : IsIdentity C B q e
      · simpa only [cutTail, if_pos hi] using
          Relation.ReflTransGen.single (ListRed.delete e [] hi)
      · simp only [cutTail, if_neg hi]
        exact .refl
    | cons d l =>
      exact ih.lift (List.cons e) (fun _ _ h ↦ ListRed.cons e h)

theorem trimEndpoints_reduces {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q)) :
    Relation.ReflTransGen (ReverseEncodedRed C B q) l (trimEndpoints C B l) :=
  (cutHead_reduces C B l).trans (cutTail_reduces C B (cutHead C B l))

def singletonTrim {q : SimplexCategoryᵒᵖ} (e : Edge C B q) : List (Edge C B q) := by
  classical
  exact if IsIdentity C B q e then [] else [e]

theorem cutTail_append_singleton {q : SimplexCategoryᵒᵖ}
    (l : List (Edge C B q)) (e : Edge C B q) :
    cutTail C B (l ++ [e]) = l ++ singletonTrim C B e := by
  classical
  induction l with
  | nil => simp [cutTail, singletonTrim]
  | cons d l ih =>
    cases l with
    | nil =>
      by_cases hi : IsIdentity C B q e <;> simp [cutTail, singletonTrim, hi]
    | cons f l => simpa only [List.cons_append, cutTail, List.cons.injEq, true_and] using ih

end
end DaggerAmalgamPaddedClassifier
