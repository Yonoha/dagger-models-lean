import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Products.Basic

/-! Single-factor placement uses initial objects in every other coordinate.
All hom equivalences and naturality are actual category data. -/

open CategoryTheory Limits

universe u v

namespace DaggerPlacementStructure

noncomputable section

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Include one factor with a specified initial object in the other factor. -/
def includeLeft (d : D) : C ⥤ C × D where
  obj c := (c, d)
  map f := (f, 𝟙 d)

def includeRight (c : C) : D ⥤ C × D where
  obj d := (c, d)
  map f := (𝟙 c, f)

def includeLeftAdjunction {d : D} (hd : IsInitial d) :
    includeLeft (C := C) d ⊣ CategoryTheory.Prod.fst C D :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ Y ↦ {
      toFun := fun f ↦ f.1
      invFun := fun f ↦ (f, hd.to Y.2)
      left_inv := fun _ ↦ Prod.ext rfl (hd.hom_ext _ _)
      right_inv := fun _ ↦ rfl }
    homEquiv_naturality_left_symm := fun _ _ ↦ Prod.ext rfl (hd.hom_ext _ _)
    homEquiv_naturality_right := fun _ _ ↦ rfl }

def includeRightAdjunction {c : C} (hc : IsInitial c) :
    includeRight (D := D) c ⊣ CategoryTheory.Prod.snd C D :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ Y ↦ {
      toFun := fun f ↦ f.2
      invFun := fun f ↦ (hc.to Y.1, f)
      left_inv := fun _ ↦ Prod.ext (hc.hom_ext _ _) rfl
      right_inv := fun _ ↦ rfl }
    homEquiv_naturality_left_symm := fun _ _ ↦ Prod.ext (hc.hom_ext _ _) rfl
    homEquiv_naturality_right := fun _ _ ↦ rfl }

/-- Projection is also a left adjoint, using a terminal object in the other factor. -/
def fstAdjunction {d : D} (hd : IsTerminal d) :
    CategoryTheory.Prod.fst C D ⊣ includeLeft (C := C) d :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X _ ↦ {
      toFun := fun f ↦ (f, hd.from X.2)
      invFun := fun f ↦ f.1
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Prod.ext rfl (hd.hom_ext _ _) }
    homEquiv_naturality_left_symm := fun _ _ ↦ rfl
    homEquiv_naturality_right := fun _ _ ↦ Prod.ext rfl (hd.hom_ext _ _) }

def sndAdjunction {c : C} (hc : IsTerminal c) :
    CategoryTheory.Prod.snd C D ⊣ includeRight (D := D) c :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X _ ↦ {
      toFun := fun f ↦ (hc.from X.1, f)
      invFun := fun f ↦ f.2
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Prod.ext (hc.hom_ext _ _) rfl }
    homEquiv_naturality_left_symm := fun _ _ ↦ rfl
    homEquiv_naturality_right := fun _ _ ↦ Prod.ext (hc.hom_ext _ _) rfl }

instance [HasTerminal D] : PreservesColimitsOfSize.{v, v} (CategoryTheory.Prod.fst C D) :=
  (fstAdjunction (C := C) terminalIsTerminal).leftAdjoint_preservesColimits

instance [HasTerminal C] : PreservesColimitsOfSize.{v, v} (CategoryTheory.Prod.snd C D) :=
  (sndAdjunction (D := D) terminalIsTerminal).leftAdjoint_preservesColimits

variable {I : Type v} [HasInitial C]

/-- Literal singleton family: the active coordinate is K, every other coordinate is initial. -/
def singleObj (i : I) (K : C) : I → C := by
  classical
  exact fun j ↦ if j = i then K else ⊥_ C

def singleMap (i : I) {K L : C} (f : K ⟶ L) : singleObj i K ⟶ singleObj i L := by
  classical
  intro j
  by_cases h : j = i
  · exact eqToHom (by simp [singleObj, h]) ≫ f ≫
      eqToHom (by simp [singleObj, h])
  · exact 𝟙 (singleObj i K j) ≫ eqToHom (by simp [singleObj, h])

def single (i : I) : C ⥤ (I → C) where
  obj := singleObj i
  map := singleMap i
  map_id K := by
    classical
    funext j
    by_cases h : j = i
    · subst j; simp [singleMap, singleObj, eqToHom_trans]
    · simp [singleMap, singleObj, h]
  map_comp f g := by
    classical
    funext j
    by_cases h : j = i
    · subst j; simp [singleMap, singleObj]
    · simp [singleMap, singleObj, h, eqToHom_trans]

def singleAtIso (i : I) (K : C) : (single i).obj K i ≅ K := by
  classical
  exact eqToIso (by simp [single, singleObj])

def singleLift (i : I) {K : C} {Y : I → C} (f : K ⟶ Y i) : (single i).obj K ⟶ Y := by
  classical
  intro j
  by_cases h : j = i
  · subst j
    exact (singleAtIso i K).hom ≫ f
  · exact eqToHom (by simp [single, singleObj, h]) ≫ initial.to (Y j)

def singleHomEquiv (i : I) (K : C) (Y : I → C) :
    ((single i).obj K ⟶ Y) ≃ (K ⟶ Y i) where
  toFun f := (singleAtIso i K).inv ≫ f i
  invFun := singleLift i
  left_inv f := by
    classical
    funext j
    by_cases h : j = i
    · subst j; simp [singleLift]
    · haveI : Subsingleton ((single i).obj K j ⟶ Y j) := by
        simpa [single, singleObj, h] using
          (inferInstance : Subsingleton (⊥_ C ⟶ Y j))
      exact Subsingleton.elim _ _
  right_inv f := by
    classical
    simp [singleLift]

def singleAdjunction (i : I) : single (C := C) i ⊣ Pi.eval (fun _ : I ↦ C) i :=
  Adjunction.mkOfHomEquiv {
    homEquiv := singleHomEquiv i
    homEquiv_naturality_left_symm := by
      classical
      intro X' X Y f g
      funext j
      by_cases h : j = i
      · subst j; simp [singleHomEquiv, singleLift, single, singleMap, singleAtIso, singleObj,
          Category.assoc]
      · haveI : Subsingleton ((single i).obj X' j ⟶ Y j) := by
          simpa [single, singleObj, h] using
            (inferInstance : Subsingleton (⊥_ C ⟶ Y j))
        exact Subsingleton.elim _ _
    homEquiv_naturality_right := by
      intro X Y Y' f g
      exact (Category.assoc _ _ _).symm }

/-- Pi evaluation is canonical functor-category evaluation under the existing full equivalence. -/
def piEvalIso (i : I) :
    (piEquivalenceFunctorDiscrete I C).functor ⋙ (evaluation (Discrete I) C).obj ⟨i⟩ ≅
      Pi.eval (fun _ : I ↦ C) i := Iso.refl _

instance [HasColimitsOfSize.{v, v} C] (i : I) :
    PreservesColimitsOfSize.{v, v} (Pi.eval (fun _ : I ↦ C) i) :=
  preservesColimits_of_natIso (piEvalIso (C := C) i)

/-- Constant initial families and diagrams have the actual initial universal property. -/
def initialFamilyIsInitial (I : Type v) : IsInitial (fun _ : I ↦ ⊥_ C) where
  desc Y i := initial.to (Y.pt i)
  fac _ j := j.as.elim
  uniq _ _ _ := by funext i; apply initial.hom_ext

end

end DaggerPlacementStructure
