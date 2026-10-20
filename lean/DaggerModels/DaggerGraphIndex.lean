import DaggerModels.Presentable

/-!
# A small index category for dagger simplicial graphs

There is one vertex object and one edge object for each simplex. The Bool label
exchanges endpoints; simplex operators are ordinary and are never reversed.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.DaggerGraphIndex

inductive Obj where
  | vertex
  | edge (n : SimplexCategory)

def Hom : Obj → Obj → Type
  | .vertex, .vertex => PUnit
  | .vertex, .edge _ => Bool
  | .edge _, .vertex => PEmpty
  | .edge n, .edge m => (n ⟶ m) × Bool

def identity : (X : Obj) → Hom X X
  | .vertex => PUnit.unit
  | .edge n => (𝟙 n, false)

def compose {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  match X, Y, Z, f, g with
  | .vertex, .vertex, .vertex, _, _ => PUnit.unit
  | .vertex, .vertex, .edge _, _, b => b
  | .vertex, .edge _, .vertex, _, h => nomatch h
  | .vertex, .edge _, .edge _, b, (_, c) => b.xor c
  | .edge _, .vertex, _, h, _ => nomatch h
  | .edge _, .edge _, .vertex, _, h => nomatch h
  | .edge _, .edge _, .edge _, (α, b), (β, c) => (α ≫ β, b.xor c)

instance : SmallCategory Obj where
  Hom := Hom
  id := identity
  comp := compose
  id_comp {X Y} f := by
    cases X <;> cases Y <;> cases f <;> simp [identity, compose]
  comp_id {X Y} f := by
    cases X <;> cases Y <;> cases f <;> simp [identity, compose]
  assoc {W X Y Z} f g h := by
    cases W <;> cases X <;> cases Y <;> cases Z
    all_goals cases f <;> cases g <;> cases h <;>
      simp [compose, Category.assoc]

def source (n : SimplexCategory) : Obj.vertex ⟶ Obj.edge n := false

def target (n : SimplexCategory) : Obj.vertex ⟶ Obj.edge n := true

def simplex {n m : SimplexCategory} (α : n ⟶ m) : Obj.edge n ⟶ Obj.edge m := (α, false)

def swap (n : SimplexCategory) : Obj.edge n ⟶ Obj.edge n := (𝟙 n, true)

@[simp] lemma source_simplex {n m : SimplexCategory} (α : n ⟶ m) :
    source n ≫ simplex α = source m := rfl

@[simp] lemma target_simplex {n m : SimplexCategory} (α : n ⟶ m) :
    target n ≫ simplex α = target m := rfl

@[simp] lemma source_swap (n : SimplexCategory) : source n ≫ swap n = target n := rfl

@[simp] lemma target_swap (n : SimplexCategory) : target n ≫ swap n = source n := rfl

@[simp] lemma swap_involutive (n : SimplexCategory) : swap n ≫ swap n = 𝟙 (Obj.edge n) := by
  change (𝟙 n ≫ 𝟙 n, true.xor true) = (𝟙 n, false)
  simp

lemma simplex_swap {n m : SimplexCategory} (α : n ⟶ m) :
    simplex α ≫ swap m = swap n ≫ simplex α := by
  change (α ≫ 𝟙 m, false.xor true) = (𝟙 n ≫ α, true.xor false)
  simp

/-- Arbitrary-value-universe presheaves on this concrete small index are LFP. -/
theorem presheavesLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} (Objᵒᵖ ⥤ Type u) := by
  let : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  let P : ObjectProperty (Type u) := ObjectProperty.singleton PUnit.{u + 1}
  let G := ObjectProperty.ofObj (fun (T : Obj × Subtype P) ↦
    Presheaf.freeYoneda T.1 T.2.1)
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
    (Objᵒᵖ ⥤ Type u) Cardinal.aleph0).2
  refine ⟨G, inferInstance,
    Presheaf.isStrongGenerator (A := Type u) typeUnitStrongGenerator.{u} Obj, ?_⟩
  rintro _ ⟨n, M, hM⟩
  have hM' : IsCardinalPresentable M Cardinal.aleph0 := by
    obtain rfl : PUnit.{u + 1} = M := by simpa [P] using hM
    exact (hasCardinalLT_of_finite PUnit.{u + 1} Cardinal.aleph0 le_rfl).isCardinalPresentable
  rw [isCardinalPresentable_iff]
  infer_instance


end DaggerModels.DaggerGraphIndex
