import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

set_option autoImplicit false

/-! Partial pushouts of the original indexed family, with all legs and universal properties. -/

open CategoryTheory Limits

universe w v u

namespace DaggerCoproductPartialBatch

variable {C : Type u} [Category.{v} C] {I : Type w}
  [HasCoproducts.{w} C] [HasPushouts C]
  (A B : I → C) (p : ∀ i, A i ⟶ B i) {X : C} (a : ∀ i, A i ⟶ X)

/-- The coproduct of the same original cells in S. -/
noncomputable def cellMap (S : Set I) : (∐ fun i : S ↦ A i.1) ⟶ ∐ fun i : S ↦ B i.1 :=
  Limits.Sigma.map (fun i : S ↦ p i.1)

/-- The original attaching maps, restricted to S. -/
noncomputable def attaching (S : Set I) : (∐ fun i : S ↦ A i.1) ⟶ X :=
  Sigma.desc (fun i : S ↦ a i.1)

/-- The actual pushout of the partial original batch. -/
noncomputable abbrev batch (S : Set I) : C :=
  pushout (attaching A a S) (cellMap A B p S)

noncomputable def base (S : Set I) : X ⟶ batch A B p a S :=
  pushout.inl (attaching A a S) (cellMap A B p S)

noncomputable def cell (S : Set I) (i : S) : B i.1 ⟶ batch A B p a S :=
  Sigma.ι (fun j : S ↦ B j.1) i ≫ pushout.inr (attaching A a S) (cellMap A B p S)

theorem relation (S : Set I) (i : S) :
    a i.1 ≫ base A B p a S = p i.1 ≫ cell A B p a S i := by
  simpa [attaching, cellMap, base, cell, Category.assoc] using
    congrArg (fun f ↦ Sigma.ι (fun j : S ↦ A j.1) i ≫ f)
      (IsPushout.of_hasPushout (attaching A a S) (cellMap A B p S)).w

/-- Desc to any target with the entire original base leg and every original cell leg. -/
noncomputable def desc (S : Set I) {Z : C} (m : X ⟶ Z) (b : ∀ i : S, B i.1 ⟶ Z)
    (h : ∀ i : S, a i.1 ≫ m = p i.1 ≫ b i) : batch A B p a S ⟶ Z :=
  (IsPushout.of_hasPushout (attaching A a S) (cellMap A B p S)).desc m (Sigma.desc b) (by
    apply Sigma.hom_ext
    intro i
    simpa [attaching, cellMap, Category.assoc] using h i)

@[reassoc (attr := simp)]
theorem base_desc (S : Set I) {Z : C} (m : X ⟶ Z) (b : ∀ i : S, B i.1 ⟶ Z)
    (h : ∀ i : S, a i.1 ≫ m = p i.1 ≫ b i) :
    base A B p a S ≫ desc A B p a S m b h = m := by
  simp [base, desc]

@[reassoc (attr := simp)]
theorem cell_desc (S : Set I) {Z : C} (m : X ⟶ Z) (b : ∀ i : S, B i.1 ⟶ Z)
    (h : ∀ i : S, a i.1 ≫ m = p i.1 ≫ b i) (i : S) :
    cell A B p a S i ≫ desc A B p a S m b h = b i := by
  simp [cell, desc, Category.assoc]

theorem hom_ext (S : Set I) {Z : C} {f g : batch A B p a S ⟶ Z}
    (hbase : base A B p a S ≫ f = base A B p a S ≫ g)
    (hcell : ∀ i : S, cell A B p a S i ≫ f = cell A B p a S i ≫ g) : f = g := by
  apply (IsPushout.of_hasPushout (attaching A a S) (cellMap A B p S)).hom_ext hbase
  apply Sigma.hom_ext
  intro i
  simpa [cell, Category.assoc] using hcell i

theorem desc_unique (S : Set I) {Z : C} (m : X ⟶ Z) (b : ∀ i : S, B i.1 ⟶ Z)
    (h : ∀ i : S, a i.1 ≫ m = p i.1 ≫ b i) (f : batch A B p a S ⟶ Z)
    (hm : base A B p a S ≫ f = m) (hb : ∀ i, cell A B p a S i ≫ f = b i) :
    f = desc A B p a S m b h := by
  apply hom_ext A B p a S
  · simpa using hm
  · intro i
    simpa using hb i

/-- Transition between two subsets uses the same original X and B_i legs. -/
noncomputable def transition {S T : Set I} (hST : S ⊆ T) :
    batch A B p a S ⟶ batch A B p a T :=
  desc A B p a S (base A B p a T)
    (fun i ↦ cell A B p a T ⟨i.1, hST i.2⟩)
    (fun i ↦ relation A B p a T ⟨i.1, hST i.2⟩)

@[reassoc (attr := simp)]
theorem base_transition {S T : Set I} (hST : S ⊆ T) :
    base A B p a S ≫ transition A B p a hST = base A B p a T := by
  simp [transition]

@[reassoc (attr := simp)]
theorem cell_transition {S T : Set I} (hST : S ⊆ T) (i : S) :
    cell A B p a S i ≫ transition A B p a hST = cell A B p a T ⟨i.1, hST i.2⟩ := by
  simp [transition]

@[simp]
theorem transition_id (S : Set I) : transition A B p a (Set.Subset.refl S) = 𝟙 _ := by
  apply hom_ext A B p a S <;> simp

theorem transition_comp {S T U : Set I} (hST : S ⊆ T) (hTU : T ⊆ U) :
    transition A B p a hST ≫ transition A B p a hTU =
      transition A B p a (hST.trans hTU) := by
  apply hom_ext A B p a S <;> simp

/-- The new singleton leg retains the original B_i; old legs retain their original indices. -/
noncomputable def singletonLeg (S : Set I) (i : I) {Z : C}
    (m : batch A B p a S ⟶ Z) (b : B i ⟶ Z) (j : (insert i S : Set I)) : B j.1 ⟶ Z := by
  classical
  by_cases h : j.1 = i
  · exact eqToHom (congrArg B h) ≫ b
  · exact cell A B p a S ⟨j.1, (Set.mem_insert_iff.mp j.2).resolve_left h⟩ ≫ m

@[simp]
theorem singletonLeg_new (S : Set I) (i : I) {Z : C}
    (m : batch A B p a S ⟶ Z) (b : B i ⟶ Z) :
    singletonLeg A B p a S i m b ⟨i, Set.mem_insert i S⟩ = b := by
  simp [singletonLeg]

theorem singletonLeg_old (S : Set I) (i : I) (hi : i ∉ S) {Z : C}
    (m : batch A B p a S ⟶ Z) (b : B i ⟶ Z) (j : S) :
    singletonLeg A B p a S i m b ⟨j.1, Set.mem_insert_of_mem i j.2⟩ =
      cell A B p a S j ≫ m := by
  have hji : j.1 ≠ i := fun h ↦ hi (h ▸ j.2)
  simp [singletonLeg, hji]

theorem singletonLeg_relation (S : Set I) (i : I) {Z : C}
    (m : batch A B p a S ⟶ Z) (b : B i ⟶ Z)
    (h : (a i ≫ base A B p a S) ≫ m = p i ≫ b) (j : (insert i S : Set I)) :
    a j.1 ≫ (base A B p a S ≫ m) = p j.1 ≫ singletonLeg A B p a S i m b j := by
  classical
  by_cases hji : j.1 = i
  · rcases j with ⟨j, hj⟩
    dsimp at hji
    subst j
    simpa [singletonLeg, Category.assoc] using h
  · have hj : j.1 ∈ S := (Set.mem_insert_iff.mp j.2).resolve_left hji
    simpa [singletonLeg, hji, Category.assoc] using
      congrArg (fun f ↦ f ≫ m) (relation A B p a S ⟨j.1, hj⟩)

noncomputable def singletonDesc (S : Set I) (i : I) {Z : C}
    (m : batch A B p a S ⟶ Z) (b : B i ⟶ Z)
    (h : (a i ≫ base A B p a S) ≫ m = p i ≫ b) : batch A B p a (insert i S) ⟶ Z :=
  desc A B p a (insert i S) (base A B p a S ≫ m) (singletonLeg A B p a S i m b)
    (singletonLeg_relation A B p a S i m b h)

/-- The entire old-batch leg, not just its individual generators, factors as m. -/
@[reassoc (attr := simp)]
theorem transition_singletonDesc (S : Set I) (i : I) (hi : i ∉ S) {Z : C}
    (m : batch A B p a S ⟶ Z) (b : B i ⟶ Z)
    (h : (a i ≫ base A B p a S) ≫ m = p i ≫ b) :
    transition A B p a (Set.subset_insert i S) ≫ singletonDesc A B p a S i m b h = m := by
  apply hom_ext A B p a S
  · simp [singletonDesc]
  · intro j
    simpa [singletonDesc] using singletonLeg_old A B p a S i hi m b j

@[reassoc (attr := simp)]
theorem new_singletonDesc (S : Set I) (i : I) {Z : C}
    (m : batch A B p a S ⟶ Z) (b : B i ⟶ Z)
    (h : (a i ≫ base A B p a S) ≫ m = p i ≫ b) :
    cell A B p a (insert i S) ⟨i, Set.mem_insert i S⟩ ≫
      singletonDesc A B p a S i m b h = b := by
  simp [singletonDesc]

theorem singletonDesc_unique (S : Set I) (i : I) {Z : C}
    (m : batch A B p a S ⟶ Z) (b : B i ⟶ Z)
    (h : (a i ≫ base A B p a S) ≫ m = p i ≫ b)
    (f : batch A B p a (insert i S) ⟶ Z)
    (hm : transition A B p a (Set.subset_insert i S) ≫ f = m)
    (hb : cell A B p a (insert i S) ⟨i, Set.mem_insert i S⟩ ≫ f = b) :
    f = singletonDesc A B p a S i m b h := by
  classical
  apply hom_ext A B p a (insert i S)
  · calc
      base A B p a (insert i S) ≫ f =
          (base A B p a S ≫ transition A B p a (Set.subset_insert i S)) ≫ f := by simp
      _ = base A B p a S ≫ m := by rw [Category.assoc, hm]
      _ = base A B p a (insert i S) ≫ singletonDesc A B p a S i m b h := by
        simp [singletonDesc]
  · intro j
    by_cases hji : j.1 = i
    · rcases j with ⟨j, hj⟩
      dsimp at hji
      subst j
      simpa using hb
    · have hj : j.1 ∈ S := (Set.mem_insert_iff.mp j.2).resolve_left hji
      have hcell := congrArg (fun t ↦ cell A B p a S ⟨j.1, hj⟩ ≫ t) hm
      simpa [singletonDesc, singletonLeg, hji, Category.assoc] using hcell

theorem singleton_square (S : Set I) (i : I) :
    (a i ≫ base A B p a S) ≫ transition A B p a (Set.subset_insert i S) =
      p i ≫ cell A B p a (insert i S) ⟨i, Set.mem_insert i S⟩ := by
  simpa using relation A B p a (insert i S) ⟨i, Set.mem_insert i S⟩

/-- Adding an index outside S is an actual pushout of the unchanged original map p_i. -/
theorem singleton_isPushout (S : Set I) (i : I) (hi : i ∉ S) :
    IsPushout (a i ≫ base A B p a S) (p i)
      (transition A B p a (Set.subset_insert i S))
      (cell A B p a (insert i S) ⟨i, Set.mem_insert i S⟩) := by
  exact IsPushout.of_isColimit (PushoutCocone.IsColimit.mk (singleton_square A B p a S i)
    (fun s ↦ singletonDesc A B p a S i s.inl s.inr s.condition)
    (fun s ↦ transition_singletonDesc A B p a S i hi s.inl s.inr s.condition)
    (fun s ↦ new_singletonDesc A B p a S i s.inl s.inr s.condition)
    (fun s m hm hb ↦ singletonDesc_unique A B p a S i s.inl s.inr s.condition m hm hb))

end DaggerCoproductPartialBatch
