import ChosenNecklacePaths

open CategoryTheory EnrichedCategory EnrichedOrdinaryCategory MonoidalCategory

open scoped Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

variable {T : NecklaceCode}

instance (a b : NecklaceThickening.{u} T) : Category (a ⟶ b) :=
  inferInstanceAs (Category (JointPath a.as b.as))

def compFunctor (a b c : NecklaceThickening.{u} T) : (a ⟶ b) × (b ⟶ c) ⥤ (a ⟶ c) where
  obj x := x.1 ≫ x.2
  map h := ⟨⟨⟨Set.union_subset_union h.1.1.1.1 h.2.1.1.1⟩⟩⟩

abbrev pathHom (a b : NecklaceThickening.{u} T) : SSet.{u} := nerve (a ⟶ b)

abbrev pathId (a : NecklaceThickening.{u} T) : 𝟙_ SSet.{u} ⟶ pathHom a a :=
  ⟨fun _ _ ↦ (Functor.const _).obj (𝟙 a), fun _ _ _ ↦ by simp; rfl⟩

abbrev pathComp (a b c : NecklaceThickening.{u} T) :
    pathHom a b ⊗ pathHom b c ⟶ pathHom a c :=
  ⟨fun _ x ↦ x.1.prod' x.2 ⋙ compFunctor a b c, fun _ _ _ ↦ by simp; rfl⟩

attribute [local ext (iff := false)] CategoryTheory.Functor.ext

@[simp] theorem pathId_comp (a b : NecklaceThickening.{u} T) :
    (λ_ (pathHom a b)).inv ≫ pathId a ▷ pathHom a b ≫ pathComp a a b = 𝟙 _ := by
  ext q x
  exact CategoryTheory.Functor.ext (fun i ↦ Category.id_comp (x.obj i))

@[simp] theorem pathComp_id (a b : NecklaceThickening.{u} T) :
    (ρ_ (pathHom a b)).inv ≫ pathHom a b ◁ pathId b ≫ pathComp a b b = 𝟙 _ := by
  ext q x
  exact CategoryTheory.Functor.ext (fun i ↦ Category.comp_id (x.obj i))

@[simp] theorem pathComp_assoc (a b c d : NecklaceThickening.{u} T) :
    (α_ (pathHom a b) (pathHom b c) (pathHom c d)).inv ≫
        pathComp a b c ▷ pathHom c d ≫ pathComp a c d =
      pathHom a b ◁ pathComp b c d ≫ pathComp a b d := by
  ext q x
  exact CategoryTheory.Functor.ext (fun i ↦
    Category.assoc (x.1.obj i) (x.2.1.obj i) (x.2.2.obj i))

instance (T : NecklaceCode) : SimplicialCategory (NecklaceThickening.{u} T) where
  Hom := pathHom
  id := pathId
  comp := pathComp
  id_comp := pathId_comp
  comp_id := pathComp_id
  assoc := pathComp_assoc
  homEquiv {a b} := nerveEquiv.symm.trans (SSet.unitHomEquiv (pathHom a b)).symm

def NC (T : NecklaceCode) : DaggerModels.SimplicialCat.{u, u} :=
  DaggerModels.SimplicialCat.of (NecklaceThickening.{u} T)

theorem NC_hom (a b : NecklaceThickening.{u} T) :
    (a ⟶[SSet.{u}] b) = nerve (a ⟶ b) := rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
