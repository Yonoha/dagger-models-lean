import FixedCategoryColimits
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Connected colimits of the original literal-O dagger categories retain every ambient leg.
The arbitrary ambient target is pulled back along its actual common vertex function. -/

open CategoryTheory Limits MonoidalCategory DaggerModels

universe u

namespace DaggerFixedCategoryConnectedColimits

noncomputable section

variable {O : Type u}

/-- Pull back the original full enrichment along the same function. -/
def reindexEnriched (D : DaggerSimplicialCat.{u, u}) (φ : O → D.Obj) :
    EnrichedCategory SSet.{u} O where
  Hom := fun a b ↦ D.enriched.Hom (φ a) (φ b)
  id := fun a ↦ D.enriched.id (φ a)
  comp := fun a b c ↦ D.enriched.comp (φ a) (φ b) (φ c)
  id_comp := fun a b ↦ D.enriched.id_comp (φ a) (φ b)
  comp_id := fun a b ↦ D.enriched.comp_id (φ a) (φ b)
  assoc := fun a b c d ↦ D.enriched.assoc (φ a) (φ b) (φ c) (φ d)

/-- The pulled-back dagger retains exactly the original target's entire dagger data. -/
def reindex (D : DaggerSimplicialCat.{u, u}) (φ : O → D.Obj) : FixedDaggerSimplicialCat O := by
  letI := reindexEnriched D φ
  exact { enriched := reindexEnriched D φ, daggerStructure :=
    { dagger := fun a b ↦ D.daggerStructure.dagger (φ a) (φ b)
      dagger_involutive := fun a b ↦ D.daggerStructure.dagger_involutive (φ a) (φ b)
      dagger_id := fun a ↦ D.daggerStructure.dagger_id (φ a)
      dagger_comp := fun a b c ↦ D.daggerStructure.dagger_comp (φ a) (φ b) (φ c) } }

/-- The actual inclusion has object function φ and identity on every original Hom space. -/
def inclusion (D : DaggerSimplicialCat.{u, u}) (φ : O → D.Obj) : (reindex D φ).toCat ⟶ D where
  obj := φ
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl
  map_dagger _ _ := by simp; rfl

/-- Retain the complete ambient enriched dagger map after identifying its object function. -/
def liftHom {C : FixedDaggerSimplicialCat O} {D : DaggerSimplicialCat.{u, u}}
    {φ : O → D.Obj} (F : C.toCat ⟶ D) (h : F.obj = φ) : C ⟶ reindex D φ := by
  cases h
  exact ⟨{ obj := id
           map := F.map
           map_id := F.map_id
           map_comp := F.map_comp
           map_dagger := F.map_dagger }, rfl⟩

theorem liftHom_comp_inclusion {C : FixedDaggerSimplicialCat O}
    {D : DaggerSimplicialCat.{u, u}} {φ : O → D.Obj} (F : C.toCat ⟶ D) (h : F.obj = φ) :
    (liftHom F h).val ≫ inclusion D φ = F := by
  cases h
  apply DaggerSimplicialCat.Hom.ext
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro a b
  simp [liftHom, inclusion]

theorem liftHom_inclusion {C : FixedDaggerSimplicialCat O}
    {D : DaggerSimplicialCat.{u, u}} {φ : O → D.Obj} (f : C ⟶ reindex D φ) :
    liftHom (f.val ≫ inclusion D φ) (by
      funext a
      change φ (f.val.obj a) = φ a
      rw [f.property]
      rfl) = f := by
  rcases f with ⟨⟨⟨obj, map, map_id, map_comp⟩, map_dagger⟩, h⟩
  cases h
  apply Subtype.ext
  apply DaggerSimplicialCat.Hom.ext
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro a b
  simp [liftHom, inclusion]

theorem postcomp_inclusion_injective {C : FixedDaggerSimplicialCat O}
    {D : DaggerSimplicialCat.{u, u}} {φ : O → D.Obj} (f g : C ⟶ reindex D φ)
    (h : f.val ≫ inclusion D φ = g.val ≫ inclusion D φ) : f = g := by
  rw [← liftHom_inclusion f, ← liftHom_inclusion g]
  congr 1

variable {J : Type u} [SmallCategory J] [IsConnected J]
variable {K : J ⥤ FixedDaggerSimplicialCat O}

/-- The vertex cocone uses the actual full object maps of the ambient cocone legs. -/
def vertexCocone (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) :
    Cocone ((Functor.const J).obj O) where
  pt := s.pt.Obj
  ι :=
    { app := fun j ↦ (s.ι.app j).obj
      naturality := by
        intro i j f
        funext a
        have h := congrArg (fun F ↦ F.obj a) (s.w f)
        change (s.ι.app j).obj ((K.map f).val.obj a) = (s.ι.app i).obj a at h
        rw [(K.map f).property] at h
        exact h }

/-- Connectedness produces the same original object function for all ambient legs. -/
def vertexMap (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) : O → s.pt.Obj :=
  (isColimitConstCocone J O).desc (vertexCocone s)

theorem vertexMap_leg (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) (j : J) :
    (s.ι.app j).obj = vertexMap s := by
  have h := (isColimitConstCocone J O).fac (vertexCocone s) j
  change vertexMap s = (s.ι.app j).obj at h
  exact h.symm

/-- Every leg lifts with its complete enrichment and dagger, on literal O. -/
def fixedCocone (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) : Cocone K where
  pt := reindex s.pt (vertexMap s)
  ι :=
    { app := fun j ↦ liftHom (s.ι.app j) (vertexMap_leg s j)
      naturality := by
        intro i j f
        apply postcomp_inclusion_injective
        change ((K.map f).val ≫ (liftHom (s.ι.app j) (vertexMap_leg s j)).val) ≫
          inclusion s.pt (vertexMap s) =
            (liftHom (s.ι.app i) (vertexMap_leg s i)).val ≫ inclusion s.pt (vertexMap s)
        rw [Category.assoc, liftHom_comp_inclusion, liftHom_comp_inclusion]
        exact s.w f }

theorem fixedCocone_leg (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) (j : J) :
    ((fixedCocone s).ι.app j).val ≫ inclusion s.pt (vertexMap s) = s.ι.app j :=
  liftHom_comp_inclusion _ _

/-- Use the original fixed colimit desc and the actual target inclusion. -/
def ambientDesc {c : Cocone K} (hc : IsColimit c)
    (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) : c.pt.toCat ⟶ s.pt :=
  (hc.desc (fixedCocone s)).val ≫ inclusion s.pt (vertexMap s)

theorem ambientDesc_obj {c : Cocone K} (hc : IsColimit c)
    (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) :
    (ambientDesc hc s).obj = vertexMap s := by
  funext a
  change vertexMap s ((hc.desc (fixedCocone s)).val.obj a) = vertexMap s a
  rw [(hc.desc (fixedCocone s)).property]
  rfl

theorem ambientDesc_fac {c : Cocone K} (hc : IsColimit c)
    (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) (j : J) :
    (c.ι.app j).val ≫ ambientDesc hc s = s.ι.app j := by
  dsimp only [ambientDesc]
  rw [← Category.assoc]
  change (c.ι.app j ≫ hc.desc (fixedCocone s)).val ≫ inclusion s.pt (vertexMap s) = _
  rw [hc.fac]
  exact fixedCocone_leg s j

theorem ambientDesc_unique {c : Cocone K} (hc : IsColimit c)
    (s : Cocone (K ⋙ FixedDaggerSimplicialCat.forget O)) (m : c.pt.toCat ⟶ s.pt)
    (hm : ∀ j : J, (c.ι.app j).val ≫ m = s.ι.app j) : m = ambientDesc hc s := by
  have hmobj : m.obj = vertexMap s := by
    funext a
    let j : J := Classical.arbitrary J
    have h := congrArg (fun F ↦ F.obj a) (hm j)
    change m.obj ((c.ι.app j).val.obj a) = (s.ι.app j).obj a at h
    rw [(c.ι.app j).property] at h
    exact h.trans (congrFun (vertexMap_leg s j) a)
  let lift : c.pt ⟶ (fixedCocone s).pt := liftHom m hmobj
  have hfac (j : J) : c.ι.app j ≫ lift = (fixedCocone s).ι.app j := by
    apply postcomp_inclusion_injective
    change ((c.ι.app j).val ≫ (liftHom m hmobj).val) ≫
      inclusion s.pt (vertexMap s) =
        (liftHom (s.ι.app j) (vertexMap_leg s j)).val ≫ inclusion s.pt (vertexMap s)
    rw [Category.assoc, liftHom_comp_inclusion, liftHom_comp_inclusion]
    exact hm j
  have hdesc : lift = hc.desc (fixedCocone s) :=
    hc.hom_ext (fun j ↦ (hfac j).trans (hc.fac (fixedCocone s) j).symm)
  calc
    m = lift.val ≫ inclusion s.pt (vertexMap s) := (liftHom_comp_inclusion m hmobj).symm
    _ = ambientDesc hc s :=
      congrArg (fun f : c.pt ⟶ (fixedCocone s).pt ↦ f.val ≫ inclusion s.pt (vertexMap s)) hdesc

/-- The entire arbitrary chosen fixed colimit cocone remains the actual ambient colimit. -/
def mappedCoconeIsColimit {c : Cocone K} (hc : IsColimit c) :
    IsColimit ((FixedDaggerSimplicialCat.forget O).mapCocone c) where
  desc := ambientDesc hc
  fac := ambientDesc_fac hc
  uniq := ambientDesc_unique hc

instance forgetPreservesConnected (O : Type u) (J : Type u)
    [SmallCategory J] [IsConnected J] :
    PreservesColimitsOfShape J (FixedDaggerSimplicialCat.forget O) where
  preservesColimit := ⟨fun {_c} hc ↦ ⟨mappedCoconeIsColimit hc⟩⟩

private theorem walkingSpan_isConnected : IsConnected WalkingSpan := by
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α F h j j'
  have hz : ∀ k : WalkingSpan, F k = F WalkingSpan.zero := by
    intro k
    rcases k with _ | k
    · rfl
    · cases k with
      | left => exact (h WalkingSpan.Hom.fst).symm
      | right => exact (h WalkingSpan.Hom.snd).symm
  exact (hz j).trans (hz j').symm

instance forgetPreservesPushouts (O : Type u) :
    PreservesColimitsOfShape WalkingSpan (FixedDaggerSimplicialCat.forget O) := by
  letI : IsConnected WalkingSpan := walkingSpan_isConnected
  letI : Category (ULift.{u} WalkingSpan) := uliftCategory WalkingSpan
  letI : PreservesColimitsOfShape (ULiftHom.{u} (ULift.{u} WalkingSpan))
      (FixedDaggerSimplicialCat.forget O) :=
    forgetPreservesConnected O (ULiftHom.{u} (ULift.{u} WalkingSpan))
  exact preservesColimitsOfShape_of_equiv
    (ULiftHomULiftCategory.equiv.{u, u} WalkingSpan).symm _

theorem map_isPushout {A B C D : FixedDaggerSimplicialCat O}
    {f : A ⟶ B} {g : A ⟶ C} {p : B ⟶ D} {q : C ⟶ D} (sq : IsPushout f g p q) :
    IsPushout f.val g.val p.val q.val := sq.map (FixedDaggerSimplicialCat.forget O)

end

end DaggerFixedCategoryConnectedColimits
