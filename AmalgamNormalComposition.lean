import AmalgamNormalForms

/-! Original quotient identities, composition and factor legs in normal coordinates. -/

open CategoryTheory MonoidalCategory DaggerModels
open DaggerAmalgamPresentation DaggerAmalgamReduction Relation

universe u

namespace DaggerAmalgamNormalForms

noncomputable section

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)

/-- Nil is irreducible in the actual relation, including the glued-object loop. -/
theorem normal_nil (q : SimplexCategoryᵒᵖ) (a : Objects B B' b b') :
    Normal B B' b b' q (.nil : Path B B' b b' q a a) := by
  intro p h
  have hh := length_lt B B' b b' h
  simp at hh

def id (q : SimplexCategoryᵒᵖ) (a : Objects B B' b b') : NormalPath B B' b b' q a a :=
  ⟨.nil, normal_nil B B' b b' q a⟩

@[simp] theorem normalize_nil (q : SimplexCategoryᵒᵖ) (a : Objects B B' b b') :
    normalize B B' b b' (.nil : Path B B' b b' q a a) = id B B' b b' q a :=
  normalize_of_normal B B' b b' (id B B' b b' q a)

/-- Concatenate the actual typed paths, then normalize the SAME quotient class. -/
def comp {q : SimplexCategoryᵒᵖ} {a s z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a s) (v : NormalPath B B' b b' q s z) :
    NormalPath B B' b b' q a z := normalize B B' b b' (p.val.comp v.val)

/-- Decoding this composition is exactly the original enriched quotient composition. -/
theorem comp_decode {q : SimplexCategoryᵒᵖ} {a s z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a s) (v : NormalPath B B' b b' q s z) :
    (homEquiv B B' b b' q a z).symm (comp B B' b b' p v) =
      (SimplicialCat.HomQuotient.comp (relations B B' b b') a s z).app q
        ((homEquiv B B' b b' q a s).symm p, (homEquiv B B' b b' q s z).symm v) :=
  mk_normalize B B' b b' (p.val.comp v.val)

theorem homEquiv_comp {q : SimplexCategoryᵒᵖ} {a s z : Objects B B' b b'}
    (h : SimplicialCat.HomQuotient.HomObj (relations B B' b b') q a s)
    (k : SimplicialCat.HomQuotient.HomObj (relations B B' b b') q s z) :
    homEquiv B B' b b' q a z
      ((SimplicialCat.HomQuotient.comp (relations B B' b b') a s z).app q (h, k)) =
        comp B B' b b' (homEquiv B B' b b' q a s h) (homEquiv B B' b b' q s z k) := by
  apply (homEquiv B B' b b' q a z).symm.injective
  rw [Equiv.symm_apply_apply, comp_decode, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Normalizing either context before concatenation preserves the exact normal form. -/
theorem normalize_comp {q : SimplexCategoryᵒᵖ} {a s z : Objects B B' b b'}
    (p : Path B B' b b' q a s) (v : Path B B' b b' q s z) :
    normalize B B' b b' (p.comp v) =
      comp B B' b b' (normalize B B' b b' p) (normalize B B' b b' v) :=
  homEquiv_comp B B' b b'
    (SimplicialCat.HomQuotient.mk _ q p) (SimplicialCat.HomQuotient.mk _ q v)

@[simp] theorem id_comp {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a z) : comp B B' b b' (id B B' b b' q a) p = p := by
  change normalize B B' b b' (Quiver.Path.nil.comp p.val) = p
  rw [Quiver.Path.nil_comp, normalize_of_normal]

@[simp] theorem comp_id {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a z) : comp B B' b b' p (id B B' b b' q z) = p := by
  change normalize B B' b b' (p.val.comp Quiver.Path.nil) = p
  rw [Quiver.Path.comp_nil, normalize_of_normal]

theorem comp_assoc {q : SimplexCategoryᵒᵖ} {a s t z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a s) (v : NormalPath B B' b b' q s t)
    (w : NormalPath B B' b b' q t z) :
    comp B B' b b' (comp B B' b b' p v) w =
      comp B B' b b' p (comp B B' b b' v w) := by
  apply (homEquiv B B' b b' q a z).symm.injective
  simp only [comp_decode]
  exact @Category.assoc
    (CategoryTheory.Quotient (SimplicialCat.HomQuotient.degreeRel (relations B B' b b') q))
    _ ⟨a⟩ ⟨s⟩ ⟨t⟩ ⟨z⟩ _ _ _

/-- Normalization is applied after every original singleton, even identity simplices. -/
def singleton (q : SimplexCategoryᵒᵖ) {a z : Objects B B' b b'}
    (e : (graphHom B B' b b' a z).obj q) : NormalPath B B' b b' q a z :=
  normalize B B' b b' (Quiver.Hom.toPath e)

@[simp] theorem homEquiv_singleton (q : SimplexCategoryᵒᵖ) {a z : Objects B B' b b'}
    (e : (graphHom B B' b b' a z).obj q) :
    homEquiv B B' b b' q a z (SimplicialCat.HomQuotient.mk _ q (Quiver.Hom.toPath e)) =
      singleton B B' b b' q e := rfl

/-- Every original color/factor map has this literal normal-representative formula. -/
theorem factor_leg (c : Bool) (q : SimplexCategoryᵒᵖ) {x y : (factor B B' c).Obj}
    (h : (x ⟶[SSet] y).obj q) :
    homEquiv B B' b b' q (label B B' b b' c x) (label B B' b b' c y)
      (((leg B B' b b' c).map x y).app q h) =
        normalize B B' b b' (factorPath B B' b b' c q h) := rfl

theorem factor_identity (c : Bool) (q : SimplexCategoryᵒᵖ) (x : (factor B B' c).Obj) :
    normalize B B' b b' (factorPath B B' b b' c q ((eId SSet x).app q PUnit.unit)) =
      id B B' b b' q (label B B' b b' c x) := by
  rw [← normalize_nil B B' b b']
  exact normalize_finite B B' b b' (.single (HomRel.CompClosure.of (Rel.factorId c x)))

theorem factor_composition (c : Bool) (q : SimplexCategoryᵒᵖ)
    {x y z : (factor B B' c).Obj} (h : (x ⟶[SSet] y).obj q) (k : (y ⟶[SSet] z).obj q) :
    comp B B' b b' (normalize B B' b b' (factorPath B B' b b' c q h))
      (normalize B B' b b' (factorPath B B' b b' c q k)) =
        normalize B B' b b' (factorPath B B' b b' c q ((eComp SSet x y z).app q (h, k))) := by
  rw [← normalize_comp]
  exact normalize_finite B B' b b' (.single (HomRel.CompClosure.of (Rel.factorComp c h k)))

/-- Both inverse simplicial maps retain the SAME original common-parameter composition. -/
theorem map_comp_normal {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a s z : Objects B B' b b'} (p : NormalPath B B' b b' q a s)
    (v : NormalPath B B' b b' q s z) :
    map B B' b b' α (comp B B' b b' p v) =
      comp B B' b b' (map B B' b b' α p) (map B B' b b' α v) := by
  rw [comp, normalize_raw_map, SimplicialColimitsFree.Paths.map_pathComp, normalize_comp]
  rfl

theorem map_id_normal {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a : Objects B B' b b') :
    map B B' b b' α (id B B' b b' q a) = id B B' b b' q' a := by
  change normalize B B' b b' (SimplicialColimitsFree.Paths.map _ α Quiver.Path.nil) = _
  rw [SimplicialColimitsFree.Paths.map_nil, normalize_nil]

/-- Full enriched identity in normal coordinates. -/
def identity (a : Objects B B' b b') : 𝟙_ SSet.{u} ⟶ normalHom B B' b b' a a where
  app q _ := id B B' b b' q a
  naturality := by
    intro q q' α
    funext e
    exact (map_id_normal B B' b b' α a).symm

/-- Full enriched composition in normal coordinates, with the original parameter order. -/
def composition (a s z : Objects B B' b b') :
    normalHom B B' b b' a s ⊗ normalHom B B' b b' s z ⟶ normalHom B B' b b' a z where
  app _ p := comp B B' b b' p.1 p.2
  naturality := by
    intro q q' α
    funext p
    exact (map_comp_normal B B' b b' α p.1 p.2).symm

theorem homIso_identity (a : Objects B B' b b') :
    SimplicialCat.HomQuotient.id (relations B B' b b') a ≫ (homIso B B' b b' a a).hom =
      identity B B' b b' a := by
  ext q e
  exact normalize_nil B B' b b' q a

theorem homIso_composition (a s z : Objects B B' b b') :
    SimplicialCat.HomQuotient.comp (relations B B' b b') a s z ≫
      (homIso B B' b b' a z).hom =
        ((homIso B B' b b' a s).hom ⊗ₘ (homIso B B' b b' s z).hom) ≫
          composition B B' b b' a s z := by
  ext q p
  exact homEquiv_comp B B' b b' p.1 p.2

theorem homIso_inverse_identity (a : Objects B B' b b') :
    identity B B' b b' a ≫ (homIso B B' b b' a a).inv =
      SimplicialCat.HomQuotient.id (relations B B' b b') a := by
  ext q e
  rfl

theorem homIso_inverse_composition (a s z : Objects B B' b b') :
    composition B B' b b' a s z ≫ (homIso B B' b b' a z).inv =
      ((homIso B B' b b' a s).inv ⊗ₘ (homIso B B' b b' s z).inv) ≫
        SimplicialCat.HomQuotient.comp (relations B B' b b') a s z := by
  ext q p
  exact comp_decode B B' b b' p.1 p.2

end
end DaggerAmalgamNormalForms
