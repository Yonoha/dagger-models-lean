import AmalgamReductionDiamond
import NormalFormQuotient

/-! Normal representatives of the SAME actual two-color contextual hom quotient.
Every endpoint and simplex degree is retained; no dagger or rank is introduced. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction Relation

universe u

namespace DaggerAmalgamNormalForms

noncomputable section

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)

abbrev Normal (q : SimplexCategoryᵒᵖ) {a z : Objects B B' b b'}
    (p : Path B B' b b' q a z) : Prop :=
  DaggerNormalFormQuotient.Normal (Red B B' b b' q a z) p

abbrev NormalPath (q : SimplexCategoryᵒᵖ) (a z : Objects B B' b b') :=
  {p : Path B B' b b' q a z // Normal B B' b b' q p}

/-- The existing generic choice, with the proved actual reverse well-founded relation. -/
def normalize {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : Path B B' b b' q a z) : NormalPath B B' b b' q a z :=
  DaggerNormalFormQuotient.normalForm (Red B B' b b' q a z)
    (reverse_wellFounded B B' b b' q a z) p

theorem exists_normal (q : SimplexCategoryᵒᵖ) {a z : Objects B B' b b'}
    (p : Path B B' b b' q a z) :
    ∃ n, ReflTransGen (Red B B' b b' q a z) p n ∧ Normal B B' b b' q n :=
  DaggerNormalFormQuotient.exists_normal _ (reverse_wellFounded B B' b b' q a z) p

theorem normalForm_reduces {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : Path B B' b b' q a z) :
    ReflTransGen (Red B B' b b' q a z) p (normalize B B' b b' p).val :=
  DaggerNormalFormQuotient.normalForm_reduces _ (reverse_wellFounded B B' b b' q a z) p

theorem normal_unique {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    {p n m : Path B B' b b' q a z}
    (hn : ReflTransGen (Red B B' b b' q a z) p n)
    (hm : ReflTransGen (Red B B' b b' q a z) p m)
    (hN : Normal B B' b b' q n) (hM : Normal B B' b b' q m) : n = m :=
  DaggerNormalFormQuotient.normal_unique _ (strong_diamond B B' b b' q a z) hn hm hN hM

theorem normalize_finite {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    {p p' : Path B B' b b' q a z} (h : ReflTransGen (Red B B' b b' q a z) p p') :
    normalize B B' b b' p = normalize B B' b b' p' :=
  DaggerNormalFormQuotient.normalForm_finite _ (reverse_wellFounded B B' b b' q a z)
    (strong_diamond B B' b b' q a z) h

@[simp] theorem normalize_of_normal {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a z) : normalize B B' b b' p.val = p :=
  DaggerNormalFormQuotient.normalForm_of_normal _ (reverse_wellFounded B B' b b' q a z)
    (strong_diamond B B' b b' q a z) p

/-- Literally HomQuotient.HomObj = Quot Red, not a semantic kernel quotient. -/
def homEquiv (q : SimplexCategoryᵒᵖ) (a z : Objects B B' b b') :
    SimplicialCat.HomQuotient.HomObj (relations B B' b b') q a z ≃
      NormalPath B B' b b' q a z :=
  DaggerNormalFormQuotient.quotientNormalEquiv _ (reverse_wellFounded B B' b b' q a z)
    (strong_diamond B B' b b' q a z)

@[simp] theorem homEquiv_mk {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : Path B B' b b' q a z) :
    homEquiv B B' b b' q a z (SimplicialCat.HomQuotient.mk _ q p) =
      normalize B B' b b' p := rfl

@[simp] theorem homEquiv_symm {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a z) :
    (homEquiv B B' b b' q a z).symm p =
      SimplicialCat.HomQuotient.mk (relations B B' b b') q p.val := rfl

theorem homEquiv_left_inv {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (h : SimplicialCat.HomQuotient.HomObj (relations B B' b b') q a z) :
    SimplicialCat.HomQuotient.mk _ q (homEquiv B B' b b' q a z h).val = h :=
  (homEquiv B B' b b' q a z).left_inv h

theorem homEquiv_right_inv {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a z) :
    homEquiv B B' b b' q a z (SimplicialCat.HomQuotient.mk _ q p.val) = p :=
  (homEquiv B B' b b' q a z).right_inv p

theorem mk_normalize {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    (p : Path B B' b b' q a z) :
    SimplicialCat.HomQuotient.mk (relations B B' b b') q (normalize B B' b b' p).val =
      SimplicialCat.HomQuotient.mk (relations B B' b b') q p :=
  homEquiv_left_inv B B' b b' (SimplicialCat.HomQuotient.mk _ q p)

/-- An operator may introduce identities/merges, so it is followed by normalization. -/
def map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') {a z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a z) : NormalPath B B' b b' q' a z :=
  normalize B B' b b' (SimplicialColimitsFree.Paths.map (graph B B' b b') α p.val)

theorem normalize_raw_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a z : Objects B B' b b'} (p : Path B B' b b' q a z) :
    map B B' b b' α (normalize B B' b b' p) =
      normalize B B' b b' (SimplicialColimitsFree.Paths.map (graph B B' b b') α p) :=
  DaggerNormalFormQuotient.normalForm_map _ (reverse_wellFounded B B' b b' q a z)
    _ (reverse_wellFounded B B' b b' q' a z) (strong_diamond B B' b b' q' a z)
    (SimplicialColimitsFree.Paths.map (graph B B' b b') α)
    (fun _ _ h ↦ .single (red_map B B' b b' α h)) p

/-- The actual quotient operator, on every original Hom simplex. -/
theorem normalize_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a z : Objects B B' b b'}
    (h : SimplicialCat.HomQuotient.HomObj (relations B B' b b') q a z) :
    homEquiv B B' b b' q' a z (SimplicialCat.HomQuotient.map _ α h) =
      map B B' b b' α (homEquiv B B' b b' q a z h) := by
  refine Quot.inductionOn h (fun p ↦ ?_)
  exact (normalize_raw_map B B' b b' α p).symm

theorem map_id (q : SimplexCategoryᵒᵖ) {a z : Objects B B' b b'}
    (p : NormalPath B B' b b' q a z) : map B B' b b' (𝟙 q) p = p := by
  dsimp [map]
  rw [SimplicialColimitsFree.Paths.map_id, normalize_of_normal]

theorem map_comp {q q' q'' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (β : q' ⟶ q'')
    {a z : Objects B B' b b'} (p : NormalPath B B' b b' q a z) :
    map B B' b b' (α ≫ β) p = map B B' b b' β (map B B' b b' α p) := by
  change normalize B B' b b' (SimplicialColimitsFree.Paths.map _ (α ≫ β) p.val) =
    map B B' b b' β (normalize B B' b b' (SimplicialColimitsFree.Paths.map _ α p.val))
  rw [normalize_raw_map, SimplicialColimitsFree.Paths.map_comp]

/-- The full normal-representative simplicial set, with all original operators. -/
def normalHom (a z : Objects B B' b b') : SSet.{u} where
  obj q := NormalPath B B' b b' q a z
  map α := map B B' b b' α
  map_id q := funext (map_id B B' b b' q)
  map_comp α β := funext (map_comp B B' b b' α β)

/-- Both component inverses assemble into a genuine simplicial-set isomorphism. -/
def homIso (a z : Objects B B' b b') :
    SimplicialCat.HomQuotient.hom (relations B B' b b') a z ≅ normalHom B B' b b' a z where
  hom := { app := fun q h ↦ homEquiv B B' b b' q a z h
           naturality := by
             intro q q' α
             funext h
             exact normalize_map B B' b b' α h }
  inv := { app := fun q p ↦ (homEquiv B B' b b' q a z).symm p
           naturality := by
             intro q q' α
             funext p
             change SimplicialCat.HomQuotient.mk _ q'
               (map B B' b b' α p).val =
                 SimplicialCat.HomQuotient.map (relations B B' b b') α
                   (SimplicialCat.HomQuotient.mk (relations B B' b b') q p.val)
             exact mk_normalize B B' b b' _ }
  hom_inv_id := by ext q h; exact homEquiv_left_inv B B' b b' h
  inv_hom_id := by ext q p; exact homEquiv_right_inv B B' b b' p

end
end DaggerAmalgamNormalForms
