import DaggerModels.ReverseSimplex
import DaggerModels.SimplicialSet

/-!
# Dagger simplicial sets as reversal presheaves

This module constructs the equivalence in Part I,
`prop.sSetdag_is_equivalent_to_Fun`, using the category of actual functions
from `ReverseSimplex`. The agreement of the two orientations on constant
functions uses the requirement that the dagger fixes vertices.
-/

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels

namespace ReverseSimplex

/-- Regard a monotone reversal-simplex map as an ordinary simplex map. -/
def monotoneHom {m n : ReverseSimplex} (f : m ⟶ n) (hf : Monotone f.toFun) :
    ⦋m.len⦌ ⟶ ⦋n.len⦌ :=
  SimplexCategory.Hom.mk ⟨f.toFun, hf⟩

/-- Reverse the target of an antitone map to obtain an ordinary simplex map. -/
def antitoneHom {m n : ReverseSimplex} (f : m ⟶ n) (hf : Antitone f.toFun) :
    ⦋m.len⦌ ⟶ ⦋n.len⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ (f.toFun i).rev, fun _ _ h ↦ by
    simpa only [Fin.rev_le_rev] using hf h⟩

@[simp] theorem monotoneHom_apply {m n : ReverseSimplex} (f : m ⟶ n)
    (hf : Monotone f.toFun) (i : Fin (m.len + 1)) :
    (monotoneHom f hf).toOrderHom i = f.toFun i := rfl

@[simp] theorem antitoneHom_apply {m n : ReverseSimplex} (f : m ⟶ n)
    (hf : Antitone f.toFun) (i : Fin (m.len + 1)) :
    (antitoneHom f hf).toOrderHom i = (f.toFun i).rev := rfl

theorem antitone_factorization {m n : ReverseSimplex} (f : m ⟶ n)
    (hf : Antitone f.toFun) :
    inclusion.map (antitoneHom f hf) ≫ reversal n = f := by
  apply Hom.ext
  intro i
  exact Fin.rev_rev (f.toFun i)

theorem monotone_factorization {m n : ReverseSimplex} (f : m ⟶ n)
    (hf : Monotone f.toFun) : inclusion.map (monotoneHom f hf) = f := by
  apply Hom.ext
  intro i
  rfl

end ReverseSimplex

namespace DaggerSSet

theorem dagger_constant (X : DaggerSSet.{u}) {m n : ℕ}
    (i : Fin (n + 1)) (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex (X.toSSet.map (SimplexCategory.const ⦋m⦌ ⦋n⦌ i).op x) =
      X.toSSet.map (SimplexCategory.const ⦋m⦌ ⦋n⦌ i).op x := by
  have hrev : SimplexCategory.rev.map (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0) =
      SimplexCategory.const ⦋m⦌ ⦋0⦌ 0 := by
    exact SimplexCategory.eq_const_to_zero _
  rw [SimplexCategory.const_fac_thru_zero, op_comp, X.toSSet.map_comp]
  change X.daggerSimplex (X.toSSet.map (SimplexCategory.const ⦋m⦌ ⦋0⦌ 0).op
    (X.toSSet.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x)) = _
  rw [X.dagger_map, hrev, X.dagger_vertex]
  rfl

/-- The formulas for the two orientations agree precisely on their overlap. -/
theorem orientation_agreement (X : DaggerSSet.{u}) {m n : ReverseSimplex}
    (f : m ⟶ n) (hm : Monotone f.toFun) (ha : Antitone f.toFun)
    (x : X.toSSet _⦋n.len⦌) :
    X.toSSet.map (ReverseSimplex.monotoneHom f hm).op x =
      X.toSSet.map (ReverseSimplex.antitoneHom f ha).op (X.daggerSimplex x) := by
  have hc := (ReverseSimplex.monotone_antitone_iff_constant f.toFun).1 ⟨hm, ha⟩
  have hconst : ReverseSimplex.monotoneHom f hm =
      SimplexCategory.const ⦋m.len⦌ ⦋n.len⦌ (f.toFun 0) := by
    ext i : 3
    exact hc i 0
  have hrev : SimplexCategory.rev.map (ReverseSimplex.monotoneHom f hm) =
      ReverseSimplex.antitoneHom f ha := by
    ext i : 3
    change (f.toFun i.rev).rev = (f.toFun i).rev
    rw [hc i.rev i]
  rw [← hrev, ← X.dagger_map, hconst, X.dagger_constant]

/-- Pull back along an actual monotone or antitone function. -/
noncomputable def extensionMap (X : DaggerSSet.{u}) {m n : ReverseSimplex}
    (f : m ⟶ n) : X.toSSet _⦋n.len⦌ → X.toSSet _⦋m.len⦌ := by
  classical
  exact if hm : Monotone f.toFun then
    X.toSSet.map (ReverseSimplex.monotoneHom f hm).op
  else
    X.toSSet.map (ReverseSimplex.antitoneHom f
      (f.monotone_or_antitone.resolve_left hm)).op ∘ X.daggerSimplex

theorem extensionMap_monotone (X : DaggerSSet.{u}) {m n : ReverseSimplex}
    (f : m ⟶ n) (hf : Monotone f.toFun) (x : X.toSSet _⦋n.len⦌) :
    X.extensionMap f x = X.toSSet.map (ReverseSimplex.monotoneHom f hf).op x := by
  simp only [extensionMap, dif_pos hf]

theorem extensionMap_antitone (X : DaggerSSet.{u}) {m n : ReverseSimplex}
    (f : m ⟶ n) (hf : Antitone f.toFun) (x : X.toSSet _⦋n.len⦌) :
    X.extensionMap f x =
      X.toSSet.map (ReverseSimplex.antitoneHom f hf).op (X.daggerSimplex x) := by
  classical
  by_cases hm : Monotone f.toFun
  · rw [X.extensionMap_monotone f hm, X.orientation_agreement f hm hf]
  · simp only [extensionMap, dif_neg hm, Function.comp_apply]

theorem pullback_comp (X : DaggerSSet.{u}) {l m n : ℕ}
    (f : ⦋l⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌) (x : X.toSSet _⦋n⦌) :
    X.toSSet.map (f ≫ g).op x = X.toSSet.map f.op (X.toSSet.map g.op x) := by
  rw [op_comp, X.toSSet.map_comp]
  rfl

theorem extensionMap_id (X : DaggerSSet.{u}) (m : ReverseSimplex)
    (x : X.toSSet _⦋m.len⦌) : X.extensionMap (𝟙 m) x = x := by
  rw [X.extensionMap_monotone (𝟙 m) (fun _ _ h ↦ h)]
  have hid : ReverseSimplex.monotoneHom (𝟙 m) (fun _ _ h ↦ h) = 𝟙 ⦋m.len⦌ := rfl
  rw [hid, op_id, X.toSSet.map_id]
  rfl

theorem extensionMap_comp (X : DaggerSSet.{u}) {l m n : ReverseSimplex}
    (f : l ⟶ m) (g : m ⟶ n) (x : X.toSSet _⦋n.len⦌) :
    X.extensionMap (f ≫ g) x = X.extensionMap f (X.extensionMap g x) := by
  rcases f.monotone_or_antitone with hf | hf <;>
    rcases g.monotone_or_antitone with hg | hg
  · have hfg : Monotone (f ≫ g).toFun := fun _ _ h ↦ hg (hf h)
    have hnorm : ReverseSimplex.monotoneHom (f ≫ g) hfg =
        ReverseSimplex.monotoneHom f hf ≫ ReverseSimplex.monotoneHom g hg := rfl
    rw [X.extensionMap_monotone _ hfg, X.extensionMap_monotone _ hg,
      X.extensionMap_monotone _ hf, hnorm, X.pullback_comp]
  · have hfg : Antitone (f ≫ g).toFun := fun _ _ h ↦ hg (hf h)
    have hnorm : ReverseSimplex.antitoneHom (f ≫ g) hfg =
        ReverseSimplex.monotoneHom f hf ≫ ReverseSimplex.antitoneHom g hg := rfl
    rw [X.extensionMap_antitone _ hfg, X.extensionMap_antitone _ hg,
      X.extensionMap_monotone _ hf, hnorm, X.pullback_comp]
  · have hfg : Antitone (f ≫ g).toFun := fun _ _ h ↦ hg (hf h)
    have hnorm : ReverseSimplex.antitoneHom (f ≫ g) hfg =
        ReverseSimplex.antitoneHom f hf ≫
          SimplexCategory.rev.map (ReverseSimplex.monotoneHom g hg) := by
      ext i : 3
      change (g.toFun (f.toFun i)).rev = (g.toFun (f.toFun i).rev.rev).rev
      rw [Fin.rev_rev]
    rw [X.extensionMap_antitone _ hfg, X.extensionMap_monotone _ hg,
      X.extensionMap_antitone _ hf, hnorm, X.pullback_comp, X.dagger_map]
  · have hfg : Monotone (f ≫ g).toFun := fun _ _ h ↦ hg (hf h)
    have hnorm : ReverseSimplex.monotoneHom (f ≫ g) hfg =
        ReverseSimplex.antitoneHom f hf ≫
          SimplexCategory.rev.map (ReverseSimplex.antitoneHom g hg) := by
      ext i : 3
      change g.toFun (f.toFun i) = (g.toFun (f.toFun i).rev.rev).rev.rev
      simp only [Fin.rev_rev]
    rw [X.extensionMap_monotone _ hfg, X.extensionMap_antitone _ hg,
      X.extensionMap_antitone _ hf, hnorm, X.pullback_comp,
      X.dagger_map, X.dagger_dagger]

/-- Extend a dagger simplicial set to a presheaf on actual reversal maps. -/
noncomputable def extension (X : DaggerSSet.{u}) : ReverseSimplexᵒᵖ ⥤ Type u where
  obj n := X.toSSet _⦋n.unop.len⦌
  map f := X.extensionMap f.unop
  map_id n := by
    funext x
    exact X.extensionMap_id n.unop x
  map_comp f g := by
    funext x
    exact X.extensionMap_comp g.unop f.unop x

theorem Hom.dagger_comm {X Y : DaggerSSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (x : X.toSSet _⦋n⦌) :
    f.hom.app (op ⦋n⦌) (X.daggerSimplex x) =
      Y.daggerSimplex (f.hom.app (op ⦋n⦌) x) := by
  exact (congrFun (NatTrans.congr_app f.comm (op ⦋n⦌)) x).symm

theorem Hom.extensionMap_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    {m n : ReverseSimplex} (g : m ⟶ n) (x : X.toSSet _⦋n.len⦌) :
    f.hom.app (op ⦋m.len⦌) (X.extensionMap g x) =
      Y.extensionMap g (f.hom.app (op ⦋n.len⦌) x) := by
  rcases g.monotone_or_antitone with hg | hg
  · rw [X.extensionMap_monotone g hg, Y.extensionMap_monotone g hg]
    exact congrFun (f.hom.naturality (ReverseSimplex.monotoneHom g hg).op) x
  · rw [X.extensionMap_antitone g hg, Y.extensionMap_antitone g hg]
    have h := congrFun (f.hom.naturality (ReverseSimplex.antitoneHom g hg).op)
      (X.daggerSimplex x)
    change f.hom.app (op ⦋m.len⦌)
      (X.toSSet.map (ReverseSimplex.antitoneHom g hg).op (X.daggerSimplex x)) =
      Y.toSSet.map (ReverseSimplex.antitoneHom g hg).op
        (f.hom.app (op ⦋n.len⦌) (X.daggerSimplex x)) at h
    rw [h, f.dagger_comm]

/-- Extend a dagger-compatible simplicial map to the reversal presheaves. -/
noncomputable def extensionHom {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    X.extension ⟶ Y.extension where
  app n := f.hom.app (op ⦋n.unop.len⦌)
  naturality {n m} g := by
    funext x
    exact f.extensionMap_naturality g.unop x

/-- The functor that extends simplicial pullbacks by the dagger involution. -/
noncomputable def toPresheaf : DaggerSSet.{u} ⥤ (ReverseSimplexᵒᵖ ⥤ Type u) where
  obj := extension
  map := extensionHom
  map_id X := by ext n x; rfl
  map_comp f g := by ext n x; rfl

theorem extension_inclusion (X : DaggerSSet.{u}) {m n : SimplexCategory}
    (f : m ⟶ n) (x : X.toSSet.obj (op n)) :
    X.extension.map (ReverseSimplex.inclusion.map f).op x = X.toSSet.map f.op x := by
  rw [show X.extension.map (ReverseSimplex.inclusion.map f).op x =
    X.extensionMap (ReverseSimplex.inclusion.map f) x from rfl]
  rw [X.extensionMap_monotone _ f.toOrderHom.monotone]
  have h : ReverseSimplex.monotoneHom (ReverseSimplex.inclusion.map f)
      f.toOrderHom.monotone = f := by
    ext i : 3
    rfl
  rw [h]

theorem extension_reversal (X : DaggerSSet.{u}) (n : ReverseSimplex)
    (x : X.toSSet _⦋n.len⦌) :
    X.extension.map (ReverseSimplex.reversal n).op x = X.daggerSimplex x := by
  have ha : Antitone (ReverseSimplex.reversal n).toFun := fun _ _ h ↦ by
    simpa only [ReverseSimplex.reversal_apply, Fin.rev_le_rev] using h
  change X.extensionMap (ReverseSimplex.reversal n) x = _
  rw [X.extensionMap_antitone _ ha]
  have hid : ReverseSimplex.antitoneHom (ReverseSimplex.reversal n) ha =
      𝟙 ⦋n.len⦌ := by
    ext i : 3
    exact Fin.rev_rev i
  rw [hid, op_id, X.toSSet.map_id]
  rfl

end DaggerSSet

namespace ReversePresheaf

/-- Restriction to the ordinary simplex category, with dagger given by reversal. -/
def restriction (F : ReverseSimplexᵒᵖ ⥤ Type u) : DaggerSSet.{u} where
  toSSet := ReverseSimplex.inclusion.op ⋙ F
  dagger :=
    { app := fun n ↦ F.map (ReverseSimplex.reversal
        (ReverseSimplex.inclusion.obj n.unop)).op
      naturality := fun {n m} f ↦ by
        change F.map (ReverseSimplex.inclusion.map f.unop).op ≫
          F.map (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj m.unop)).op =
          F.map (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj n.unop)).op ≫
          F.map (ReverseSimplex.inclusion.map (SimplexCategory.rev.map f.unop)).op
        rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
        congr 2
        simpa only [SimplexCategory.rev_map_rev_map] using
          (ReverseSimplex.reversal_naturality (SimplexCategory.rev.map f.unop)).symm }
  involutive n x := by
    change F.map (ReverseSimplex.reversal (ReverseSimplex.mk n)).op
      (F.map (ReverseSimplex.reversal (ReverseSimplex.mk n)).op x) = x
    have h := congrFun (F.map_comp
      (ReverseSimplex.reversal (ReverseSimplex.mk n)).op
      (ReverseSimplex.reversal (ReverseSimplex.mk n)).op) x
    simpa only [← op_comp, ReverseSimplex.reversal_comp_reversal, op_id,
      F.map_id] using h.symm
  fixedVertices x := by
    change F.map (ReverseSimplex.reversal (ReverseSimplex.mk 0)).op x = x
    rw [ReverseSimplex.reversal_zero, op_id, F.map_id]
    rfl

/-- A natural transformation commutes with the reversals by naturality. -/
def restrictionHom {F G : ReverseSimplexᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    restriction F ⟶ restriction G where
  hom :=
    { app := fun n ↦ f.app (op (ReverseSimplex.inclusion.obj n.unop))
      naturality {n m} g := f.naturality (ReverseSimplex.inclusion.op.map g) }
  comm := by
    ext n x
    exact (congrFun (f.naturality
      (ReverseSimplex.reversal (ReverseSimplex.inclusion.obj n.unop)).op) x).symm

/-- Restrict a reversal presheaf and its natural transformations to dagger sets. -/
def toDaggerSSet : (ReverseSimplexᵒᵖ ⥤ Type u) ⥤ DaggerSSet.{u} where
  obj := restriction
  map := restrictionHom
  map_id F := by apply DaggerSSet.Hom.ext; rfl
  map_comp f g := by apply DaggerSSet.Hom.ext; rfl

theorem restriction_extension (F : ReverseSimplexᵒᵖ ⥤ Type u)
    {m n : ReverseSimplex} (f : m ⟶ n) (x : F.obj (op n)) :
    (restriction F).extension.map f.op x = F.map f.op x := by
  rcases f.monotone_or_antitone with hf | hf
  · change (restriction F).extensionMap f x = _
    rw [(restriction F).extensionMap_monotone f hf]
    change F.map (ReverseSimplex.inclusion.map
      (ReverseSimplex.monotoneHom f hf)).op x = _
    rw [ReverseSimplex.monotone_factorization]
  · change (restriction F).extensionMap f x = _
    rw [(restriction F).extensionMap_antitone f hf]
    change F.map (ReverseSimplex.inclusion.map
      (ReverseSimplex.antitoneHom f hf)).op
      (F.map (ReverseSimplex.reversal n).op x) = _
    have h := congrFun (F.map_comp (ReverseSimplex.reversal n).op
      (ReverseSimplex.inclusion.map (ReverseSimplex.antitoneHom f hf)).op) x
    change F.map ((ReverseSimplex.inclusion.map
      (ReverseSimplex.antitoneHom f hf) ≫ ReverseSimplex.reversal n).op) x =
      F.map (ReverseSimplex.inclusion.map (ReverseSimplex.antitoneHom f hf)).op
        (F.map (ReverseSimplex.reversal n).op x) at h
    rw [← h, ReverseSimplex.antitone_factorization]

end ReversePresheaf

namespace DaggerSSet

/-- Restricting the extended presheaf recovers the original dagger simplicial set. -/
noncomputable def unitComponent (X : DaggerSSet.{u}) :
    X ≅ ReversePresheaf.restriction X.extension where
  hom :=
    { hom :=
        { app := fun _ ↦ id
          naturality := fun {n m} f ↦ by
            funext x
            exact (X.extension_inclusion f.unop x).symm }
      comm := by
        ext n x
        exact X.extension_reversal (ReverseSimplex.inclusion.obj n.unop) x }
  inv :=
    { hom :=
        { app := fun _ ↦ id
          naturality := fun {n m} f ↦ by
            funext x
            exact X.extension_inclusion f.unop x }
      comm := by
        ext n x
        exact (X.extension_reversal (ReverseSimplex.inclusion.obj n.unop) x).symm }
  hom_inv_id := by apply Hom.ext; ext n x; rfl
  inv_hom_id := by apply Hom.ext; ext n x; rfl

/-- The identity maps on simplices give the natural unit isomorphism. -/
noncomputable def unitIso :
    𝟭 DaggerSSet.{u} ≅ toPresheaf ⋙ ReversePresheaf.toDaggerSSet :=
  NatIso.ofComponents unitComponent (by
    intro X Y f
    apply Hom.ext
    ext n x
    rfl)

end DaggerSSet

namespace ReversePresheaf

/-- Extending a restricted presheaf recovers every actual reversal map. -/
noncomputable def counitComponent (F : ReverseSimplexᵒᵖ ⥤ Type u) :
    (restriction F).extension ≅ F where
  hom :=
    { app := fun _ ↦ id
      naturality := fun {n m} f ↦ by
        funext x
        exact restriction_extension F f.unop x }
  inv :=
    { app := fun _ ↦ id
      naturality := fun {n m} f ↦ by
        funext x
        exact (restriction_extension F f.unop x).symm }
  hom_inv_id := by ext n x; rfl
  inv_hom_id := by ext n x; rfl

/-- The identity maps on all finite-ordinal values give the natural counit. -/
noncomputable def counitIso :
    toDaggerSSet ⋙ DaggerSSet.toPresheaf ≅ 𝟭 (ReverseSimplexᵒᵖ ⥤ Type u) :=
  NatIso.ofComponents counitComponent (by
    intro F G f
    ext n x
    rfl)

end ReversePresheaf

/-- Part I `prop.sSetdag_is_equivalent_to_Fun`: dagger simplicial sets are
presheaves on the category of actual monotone or antitone finite-ordinal maps. -/
noncomputable def daggerSSetEquivalencePresheaf :
    DaggerSSet.{u} ≌ (ReverseSimplexᵒᵖ ⥤ Type u) where
  functor := DaggerSSet.toPresheaf
  inverse := ReversePresheaf.toDaggerSSet
  unitIso := DaggerSSet.unitIso
  counitIso := ReversePresheaf.counitIso
  functor_unitIso_comp X := by ext n x; rfl

/-- The categorical-equivalence existence assertion in Part I. -/
theorem nonempty_daggerSSetEquivalencePresheaf :
    Nonempty (DaggerSSet.{u} ≌ (ReverseSimplexᵒᵖ ⥤ Type u)) :=
  ⟨daggerSSetEquivalencePresheaf⟩

end DaggerModels
