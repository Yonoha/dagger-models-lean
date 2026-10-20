import DaggerModels.DaggerSimplicialForget

/-!
# Operations on a split quotient of dagger simplicial graphs

Part I `bg.lem.presentable`: retain all object maps and descend enriched
composition through the actual split graph quotient.
-/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.DaggerSimplicialCat.SplitCoequalizer

structure GraphSplitData {A B : DaggerSimplicialCat.{u, u}} (f g : A ⟶ B)
    {Q : DaggerSimplicialGraph.{u}} (π : underlyingGraph B ⟶ Q) where
  rightSection : Q ⟶ underlyingGraph B
  leftSection : underlyingGraph B ⟶ underlyingGraph A
  condition : underlyingGraphMap f ≫ π = underlyingGraphMap g ≫ π
  rightSection_π : rightSection ≫ π = 𝟙 Q
  leftSection_bottom : leftSection ≫ underlyingGraphMap g = 𝟙 (underlyingGraph B)
  leftSection_top : leftSection ≫ underlyingGraphMap f = π ≫ rightSection

private lemma comp_obj_eq {G H K : DaggerSimplicialGraph.{u}}
    (f : G ⟶ H) (g : H ⟶ K) (k : G ⟶ K) (h : f ≫ g = k) (x : G.Obj) :
    g.obj (f.obj x) = k.obj x := congrArg (fun a : G ⟶ K ↦ a.obj x) h

variable {A B : DaggerSimplicialCat.{u, u}} {f g : A ⟶ B}
  {Q : DaggerSimplicialGraph.{u}} {π : underlyingGraph B ⟶ Q}

lemma section_obj (s : GraphSplitData f g π) (x : Q.Obj) :
    π.obj (s.rightSection.obj x) = x := comp_obj_eq _ _ _ s.rightSection_π x

/-- The actual simplicial unit, transported from the selected lift of its object. -/
def quotientId (s : GraphSplitData f g π) (x : Q.Obj) : 𝟙_ SSet.{u} ⟶ Q.Hom x x :=
  eId SSet (show B.Obj from s.rightSection.obj x) ≫
    π.map (s.rightSection.obj x) (s.rightSection.obj x) ≫
      eqToHom (by rw [section_obj s x])

/-- The actual simplicial composition of the selected pair of lifts. -/
def quotientComp (s : GraphSplitData f g π) (x y z : Q.Obj) :
    Q.Hom x y ⊗ Q.Hom y z ⟶ Q.Hom x z :=
  (s.rightSection.map x y ⊗ₘ s.rightSection.map y z) ≫
    eComp SSet (show B.Obj from s.rightSection.obj x)
      (s.rightSection.obj y) (s.rightSection.obj z) ≫
      π.map (s.rightSection.obj x) (s.rightSection.obj z) ≫
        eqToHom (by rw [section_obj s x, section_obj s z])

abbrev UnitTotal (G : DaggerSimplicialGraph.{u}) := Σ x : G.Obj, 𝟙_ SSet.{u} ⟶ G.Hom x x

def unitMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) : UnitTotal G → UnitTotal H
  | ⟨x, e⟩ => ⟨k.obj x, e ≫ k.map x x⟩

def unitDatum (C : DaggerSimplicialCat.{u, u}) (x : C.Obj) : UnitTotal (underlyingGraph C) :=
  ⟨x, eId SSet x⟩

@[simp] lemma unitMap_comp {G H K : DaggerSimplicialGraph.{u}} (a : G ⟶ H) (b : H ⟶ K)
    (e : UnitTotal G) : unitMap (a ≫ b) e = unitMap b (unitMap a e) := by
  rcases e with ⟨x, e⟩
  exact congrArg (fun h ↦ (⟨b.obj (a.obj x), h⟩ : UnitTotal K)) (Category.assoc _ _ _).symm

@[simp] lemma unitMap_functor {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    unitMap (underlyingGraphMap F) (unitDatum C x) = unitDatum D (F.obj x) := by
  exact congrArg (fun h ↦ (⟨F.obj x, h⟩ : UnitTotal (underlyingGraph D))) (F.map_id x)

private lemma unit_transport (G : DaggerSimplicialGraph.{u}) {x y : G.Obj} (h : x = y)
    (e : 𝟙_ SSet.{u} ⟶ G.Hom x x) :
    (⟨y, e ≫ eqToHom (by rw [h])⟩ : UnitTotal G) = ⟨x, e⟩ := by
  subst h
  simp

lemma quotientId_total (s : GraphSplitData f g π) (x : Q.Obj) :
    (⟨x, quotientId s x⟩ : UnitTotal Q) =
      unitMap π (unitDatum B (s.rightSection.obj x)) := by
  dsimp only [quotientId, unitMap, unitDatum]
  rw [← Category.assoc]
  exact unit_transport Q (section_obj s x) _

/-- The original unit descends along the actual quotient graph map. -/
lemma quotientId_preservation (s : GraphSplitData f g π) (x : B.Obj) :
    eId SSet x ≫ π.map x x = quotientId s (π.obj x) := by
  have hg : g.obj (s.leftSection.obj x) = x :=
    comp_obj_eq _ _ _ s.leftSection_bottom x
  have hf : f.obj (s.leftSection.obj x) = s.rightSection.obj (π.obj x) :=
    comp_obj_eq _ _ _ s.leftSection_top x
  have h : unitMap π (unitDatum B x) =
      (⟨π.obj x, quotientId s (π.obj x)⟩ : UnitTotal Q) := by
    calc
      _ = unitMap π (unitMap (underlyingGraphMap g)
          (unitDatum A (s.leftSection.obj x))) := by rw [unitMap_functor, hg]
      _ = unitMap π (unitMap (underlyingGraphMap f)
          (unitDatum A (s.leftSection.obj x))) := by
            rw [← unitMap_comp, ← unitMap_comp, s.condition]
      _ = unitMap π (unitDatum B (s.rightSection.obj (π.obj x))) := by
            rw [unitMap_functor, hf]
      _ = _ := (quotientId_total s (π.obj x)).symm
  exact eq_of_heq (Sigma.mk.inj h).2

abbrev ArrowTotal (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :=
  Σ x : G.Obj, Σ y : G.Obj, (G.Hom x y).obj n

abbrev PairTotal (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :=
  Σ x : G.Obj, Σ y : G.Obj, Σ z : G.Obj, (G.Hom x y).obj n × (G.Hom y z).obj n

def arrowMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) (n : SimplexCategoryᵒᵖ) :
    ArrowTotal G n → ArrowTotal H n
  | ⟨x, y, e⟩ => ⟨k.obj x, k.obj y, (k.map x y).app n e⟩

def pairMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) (n : SimplexCategoryᵒᵖ) :
    PairTotal G n → PairTotal H n
  | ⟨x, y, z, e₁, e₂⟩ =>
      ⟨k.obj x, k.obj y, k.obj z, (k.map x y).app n e₁, (k.map y z).app n e₂⟩

@[simp] lemma arrowMap_comp {G H K : DaggerSimplicialGraph.{u}} (a : G ⟶ H) (b : H ⟶ K)
    (n : SimplexCategoryᵒᵖ) (e : ArrowTotal G n) :
    arrowMap (a ≫ b) n e = arrowMap b n (arrowMap a n e) := rfl

@[simp] lemma pairMap_comp {G H K : DaggerSimplicialGraph.{u}} (a : G ⟶ H) (b : H ⟶ K)
    (n : SimplexCategoryᵒᵖ) (e : PairTotal G n) :
    pairMap (a ≫ b) n e = pairMap b n (pairMap a n e) := rfl

@[simp] lemma pairMap_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (e : PairTotal G n) : pairMap (𝟙 G) n e = e := by
  rcases e with ⟨x, y, z, e₁, e₂⟩
  rfl

def compDatum (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    PairTotal (underlyingGraph C) n → ArrowTotal (underlyingGraph C) n
  | ⟨x, y, z, e₁, e₂⟩ => ⟨x, z, (eComp SSet (show C.Obj from x) y z).app n (e₁, e₂)⟩

lemma compDatum_functor {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (p : PairTotal (underlyingGraph C) n) :
    arrowMap (underlyingGraphMap F) n (compDatum C n p) =
      compDatum D n (pairMap (underlyingGraphMap F) n p) := by
  rcases p with ⟨x, y, z, e₁, e₂⟩
  exact congrArg (fun e ↦ (⟨F.obj x, F.obj z, e⟩ : ArrowTotal (underlyingGraph D) n))
    (congrArg (fun h ↦ h.app n (e₁, e₂)) (F.map_comp x y z))

private lemma arrow_transport (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    {x y x' y' : G.Obj} (hx : x = x') (hy : y = y') (e : (G.Hom x y).obj n) :
    (⟨x', y', (eqToHom (by rw [hx, hy]) : G.Hom x y ⟶ G.Hom x' y').app n e⟩ :
      ArrowTotal G n) = ⟨x, y, e⟩ := by
  subst hx
  subst hy
  rfl

def quotientCompDatum (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ) :
    PairTotal Q n → ArrowTotal Q n
  | ⟨x, y, z, e₁, e₂⟩ => ⟨x, z, (quotientComp s x y z).app n (e₁, e₂)⟩

lemma quotientComp_total (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : PairTotal Q n) :
    quotientCompDatum s n p = arrowMap π n (compDatum B n (pairMap s.rightSection n p)) := by
  rcases p with ⟨x, y, z, e₁, e₂⟩
  exact arrow_transport Q n (section_obj s x) (section_obj s z) _

lemma quotientCompDatum_preservation (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : PairTotal (underlyingGraph B) n) :
    arrowMap π n (compDatum B n p) = quotientCompDatum s n (pairMap π n p) := by
  have hg : pairMap (underlyingGraphMap g) n (pairMap s.leftSection n p) = p := by
    rw [← pairMap_comp, s.leftSection_bottom, pairMap_id]
  calc
    _ = arrowMap π n (arrowMap (underlyingGraphMap g) n
        (compDatum A n (pairMap s.leftSection n p))) := by rw [compDatum_functor, hg]
    _ = arrowMap π n (arrowMap (underlyingGraphMap f) n
        (compDatum A n (pairMap s.leftSection n p))) := by
          rw [← arrowMap_comp, ← arrowMap_comp, s.condition]
    _ = arrowMap π n (compDatum B n (pairMap s.rightSection n (pairMap π n p))) := by
          rw [compDatum_functor, ← pairMap_comp, s.leftSection_top, pairMap_comp]
    _ = _ := (quotientComp_total s n (pairMap π n p)).symm

/-- Composition descends along the original quotient graph map, with all object maps retained. -/
lemma quotientComp_preservation (s : GraphSplitData f g π) (x y z : B.Obj) :
    eComp SSet x y z ≫ π.map x z =
      (π.map x y ⊗ₘ π.map y z) ≫ quotientComp s (π.obj x) (π.obj y) (π.obj z) := by
  apply NatTrans.ext
  funext n e
  have h := quotientCompDatum_preservation s n ⟨x, y, z, e⟩
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2

private lemma arrow_value_eq {G : DaggerSimplicialGraph.{u}} {n : SimplexCategoryᵒᵖ}
    {x y : G.Obj} {e e' : (G.Hom x y).obj n}
    (h : (⟨x, y, e⟩ : ArrowTotal G n) = ⟨x, y, e'⟩) : e = e' :=
  eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2

@[simp] lemma arrowMap_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (e : ArrowTotal G n) : arrowMap (𝟙 G) n e = e := by
  rcases e with ⟨x, y, e⟩
  rfl

lemma arrowMap_section (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : ArrowTotal Q n) : arrowMap π n (arrowMap s.rightSection n p) = p := by
  rw [← arrowMap_comp, s.rightSection_π, arrowMap_id]

def leftUnitPair {G : DaggerSimplicialGraph.{u}} {n : SimplexCategoryᵒᵖ}
    (ids : ∀ x : G.Obj, (G.Hom x x).obj n) : ArrowTotal G n → PairTotal G n
  | ⟨x, y, e⟩ => ⟨x, x, y, ids x, e⟩

def rightUnitPair {G : DaggerSimplicialGraph.{u}} {n : SimplexCategoryᵒᵖ}
    (ids : ∀ x : G.Obj, (G.Hom x x).obj n) : ArrowTotal G n → PairTotal G n
  | ⟨x, y, e⟩ => ⟨x, y, y, e, ids y⟩

def identityAt (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (x : (underlyingGraph C).Obj) : ((underlyingGraph C).Hom x x).obj n :=
  (eId SSet (show C.Obj from x)).app n PUnit.unit

def quotientIdentityAt (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ) (x : Q.Obj) :
    (Q.Hom x x).obj n := (quotientId s x).app n PUnit.unit

lemma leftUnitPair_map (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : ArrowTotal (underlyingGraph B) n) :
    pairMap π n (leftUnitPair (identityAt B n) p) =
      leftUnitPair (quotientIdentityAt s n) (arrowMap π n p) := by
  rcases p with ⟨x, y, e⟩
  exact congrArg (fun a ↦ (⟨π.obj x, π.obj x, π.obj y, a, (π.map x y).app n e⟩ :
    PairTotal Q n)) (congrArg (fun h ↦ h.app n PUnit.unit) (quotientId_preservation s x))

lemma rightUnitPair_map (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : ArrowTotal (underlyingGraph B) n) :
    pairMap π n (rightUnitPair (identityAt B n) p) =
      rightUnitPair (quotientIdentityAt s n) (arrowMap π n p) := by
  rcases p with ⟨x, y, e⟩
  exact congrArg (fun a ↦ (⟨π.obj x, π.obj y, π.obj y, (π.map x y).app n e, a⟩ :
    PairTotal Q n)) (congrArg (fun h ↦ h.app n PUnit.unit) (quotientId_preservation s y))

lemma compDatum_leftUnit (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (p : ArrowTotal (underlyingGraph C) n) :
    compDatum C n (leftUnitPair (identityAt C n) p) = p := by
  rcases p with ⟨x, y, e⟩
  exact congrArg (fun a ↦ (⟨x, y, a⟩ : ArrowTotal (underlyingGraph C) n))
    (congrArg (fun h ↦ h.app n e) (e_id_comp SSet (show C.Obj from x) y))

lemma compDatum_rightUnit (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (p : ArrowTotal (underlyingGraph C) n) :
    compDatum C n (rightUnitPair (identityAt C n) p) = p := by
  rcases p with ⟨x, y, e⟩
  exact congrArg (fun a ↦ (⟨x, y, a⟩ : ArrowTotal (underlyingGraph C) n))
    (congrArg (fun h ↦ h.app n e) (e_comp_id SSet (show C.Obj from x) y))

lemma quotientCompDatum_leftUnit (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : ArrowTotal Q n) :
    quotientCompDatum s n (leftUnitPair (quotientIdentityAt s n) p) = p := by
  have hp := arrowMap_section s n p
  calc
    _ = quotientCompDatum s n (leftUnitPair (quotientIdentityAt s n)
        (arrowMap π n (arrowMap s.rightSection n p))) := by rw [hp]
    _ = quotientCompDatum s n (pairMap π n
        (leftUnitPair (identityAt B n) (arrowMap s.rightSection n p))) := by
          rw [leftUnitPair_map]
    _ = arrowMap π n (compDatum B n
        (leftUnitPair (identityAt B n) (arrowMap s.rightSection n p))) :=
          (quotientCompDatum_preservation s n _).symm
    _ = p := by rw [compDatum_leftUnit, hp]

lemma quotientCompDatum_rightUnit (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : ArrowTotal Q n) :
    quotientCompDatum s n (rightUnitPair (quotientIdentityAt s n) p) = p := by
  have hp := arrowMap_section s n p
  calc
    _ = quotientCompDatum s n (rightUnitPair (quotientIdentityAt s n)
        (arrowMap π n (arrowMap s.rightSection n p))) := by rw [hp]
    _ = quotientCompDatum s n (pairMap π n
        (rightUnitPair (identityAt B n) (arrowMap s.rightSection n p))) := by
          rw [rightUnitPair_map]
    _ = arrowMap π n (compDatum B n
        (rightUnitPair (identityAt B n) (arrowMap s.rightSection n p))) :=
          (quotientCompDatum_preservation s n _).symm
    _ = p := by rw [compDatum_rightUnit, hp]

abbrev TripleTotal (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :=
  Σ w : G.Obj, Σ x : G.Obj, Σ y : G.Obj, Σ z : G.Obj,
    (G.Hom w x).obj n × (G.Hom x y).obj n × (G.Hom y z).obj n

def tripleMap {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H) (n : SimplexCategoryᵒᵖ) :
    TripleTotal G n → TripleTotal H n
  | ⟨w, x, y, z, e₁, e₂, e₃⟩ =>
      ⟨k.obj w, k.obj x, k.obj y, k.obj z,
        (k.map w x).app n e₁, (k.map x y).app n e₂, (k.map y z).app n e₃⟩

@[simp] lemma tripleMap_comp {G H K : DaggerSimplicialGraph.{u}} (a : G ⟶ H) (b : H ⟶ K)
    (n : SimplexCategoryᵒᵖ) (e : TripleTotal G n) :
    tripleMap (a ≫ b) n e = tripleMap b n (tripleMap a n e) := rfl

@[simp] lemma tripleMap_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (e : TripleTotal G n) : tripleMap (𝟙 G) n e = e := by
  rcases e with ⟨w, x, y, z, e₁, e₂, e₃⟩
  rfl

lemma tripleMap_section (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : TripleTotal Q n) : tripleMap π n (tripleMap s.rightSection n p) = p := by
  rw [← tripleMap_comp, s.rightSection_π, tripleMap_id]

def leftAssocPair {G : DaggerSimplicialGraph.{u}} {n : SimplexCategoryᵒᵖ}
    (comp : ∀ x y z, (G.Hom x y).obj n → (G.Hom y z).obj n → (G.Hom x z).obj n) :
    TripleTotal G n → PairTotal G n
  | ⟨w, x, y, z, e₁, e₂, e₃⟩ => ⟨w, y, z, comp w x y e₁ e₂, e₃⟩

def rightAssocPair {G : DaggerSimplicialGraph.{u}} {n : SimplexCategoryᵒᵖ}
    (comp : ∀ x y z, (G.Hom x y).obj n → (G.Hom y z).obj n → (G.Hom x z).obj n) :
    TripleTotal G n → PairTotal G n
  | ⟨w, x, y, z, e₁, e₂, e₃⟩ => ⟨w, x, z, e₁, comp x y z e₂ e₃⟩

def compositionAt (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (x y z : (underlyingGraph C).Obj) (e₁ : ((underlyingGraph C).Hom x y).obj n)
    (e₂ : ((underlyingGraph C).Hom y z).obj n) : ((underlyingGraph C).Hom x z).obj n :=
  (eComp SSet (show C.Obj from x) y z).app n (e₁, e₂)

def quotientCompositionAt (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (x y z : Q.Obj) (e₁ : (Q.Hom x y).obj n) (e₂ : (Q.Hom y z).obj n) :
    (Q.Hom x z).obj n := (quotientComp s x y z).app n (e₁, e₂)

lemma leftAssocPair_map (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : TripleTotal (underlyingGraph B) n) :
    pairMap π n (leftAssocPair (compositionAt B n) p) =
      leftAssocPair (quotientCompositionAt s n) (tripleMap π n p) := by
  rcases p with ⟨w, x, y, z, e₁, e₂, e₃⟩
  exact congrArg (fun a ↦ (⟨π.obj w, π.obj y, π.obj z, a, (π.map y z).app n e₃⟩ :
    PairTotal Q n)) (congrArg (fun h ↦ h.app n (e₁, e₂)) (quotientComp_preservation s w x y))

lemma rightAssocPair_map (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : TripleTotal (underlyingGraph B) n) :
    pairMap π n (rightAssocPair (compositionAt B n) p) =
      rightAssocPair (quotientCompositionAt s n) (tripleMap π n p) := by
  rcases p with ⟨w, x, y, z, e₁, e₂, e₃⟩
  exact congrArg (fun a ↦ (⟨π.obj w, π.obj x, π.obj z, (π.map w x).app n e₁, a⟩ :
    PairTotal Q n)) (congrArg (fun h ↦ h.app n (e₂, e₃)) (quotientComp_preservation s x y z))

lemma compDatum_assoc (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (p : TripleTotal (underlyingGraph C) n) :
    compDatum C n (leftAssocPair (compositionAt C n) p) =
      compDatum C n (rightAssocPair (compositionAt C n) p) := by
  rcases p with ⟨w, x, y, z, e₁, e₂, e₃⟩
  exact congrArg (fun a ↦ (⟨w, z, a⟩ : ArrowTotal (underlyingGraph C) n))
    (congrArg (fun h ↦ h.app n (e₁, e₂, e₃)) (e_assoc SSet (show C.Obj from w) x y z))

lemma quotientCompDatum_assoc (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : TripleTotal Q n) :
    quotientCompDatum s n (leftAssocPair (quotientCompositionAt s n) p) =
      quotientCompDatum s n (rightAssocPair (quotientCompositionAt s n) p) := by
  have hp := tripleMap_section s n p
  calc
    _ = quotientCompDatum s n (leftAssocPair (quotientCompositionAt s n)
        (tripleMap π n (tripleMap s.rightSection n p))) := by rw [hp]
    _ = quotientCompDatum s n (pairMap π n
        (leftAssocPair (compositionAt B n) (tripleMap s.rightSection n p))) := by
          rw [leftAssocPair_map]
    _ = arrowMap π n (compDatum B n
        (leftAssocPair (compositionAt B n) (tripleMap s.rightSection n p))) :=
          (quotientCompDatum_preservation s n _).symm
    _ = arrowMap π n (compDatum B n
        (rightAssocPair (compositionAt B n) (tripleMap s.rightSection n p))) := by
          rw [compDatum_assoc]
    _ = quotientCompDatum s n (pairMap π n
        (rightAssocPair (compositionAt B n) (tripleMap s.rightSection n p))) :=
          quotientCompDatum_preservation s n _
    _ = _ := by rw [rightAssocPair_map, hp]

/-- The split quotient carries actual enriched composition and identities. -/
def quotientEnrichedCategory (s : GraphSplitData f g π) : EnrichedCategory SSet.{u} Q.Obj where
  Hom := Q.Hom
  id := quotientId s
  comp := quotientComp s
  id_comp x y := by
    apply NatTrans.ext
    funext n e
    exact arrow_value_eq (quotientCompDatum_leftUnit s n ⟨x, y, e⟩)
  comp_id x y := by
    apply NatTrans.ext
    funext n e
    exact arrow_value_eq (quotientCompDatum_rightUnit s n ⟨x, y, e⟩)
  assoc w x y z := by
    apply NatTrans.ext
    funext n e
    rcases e with ⟨e₁, e₂, e₃⟩
    exact arrow_value_eq (quotientCompDatum_assoc s n ⟨w, x, y, z, e₁, e₂, e₃⟩)

def reverseArrow (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    ArrowTotal G n → ArrowTotal G n
  | ⟨x, y, e⟩ => ⟨y, x, (G.dagger x y).app n e⟩

def reversePair (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    PairTotal G n → PairTotal G n
  | ⟨x, y, z, e₁, e₂⟩ => ⟨z, y, x, (G.dagger y z).app n e₂, (G.dagger x y).app n e₁⟩

lemma reverseArrow_map {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) (e : ArrowTotal G n) :
    reverseArrow H n (arrowMap k n e) = arrowMap k n (reverseArrow G n e) := by
  rcases e with ⟨x, y, e⟩
  exact congrArg (fun a ↦ (⟨k.obj y, k.obj x, a⟩ : ArrowTotal H n))
    (congrArg (fun h ↦ h.app n e) (k.map_dagger x y))

lemma reversePair_map {G H : DaggerSimplicialGraph.{u}} (k : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) (e : PairTotal G n) :
    reversePair H n (pairMap k n e) = pairMap k n (reversePair G n e) := by
  rcases e with ⟨x, y, z, e₁, e₂⟩
  exact congrArg₂ (fun a b ↦ (⟨k.obj z, k.obj y, k.obj x, a, b⟩ : PairTotal H n))
    (congrArg (fun h ↦ h.app n e₂) (k.map_dagger y z))
    (congrArg (fun h ↦ h.app n e₁) (k.map_dagger x y))

def unitToArrow (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    UnitTotal G → ArrowTotal G n
  | ⟨x, e⟩ => ⟨x, x, e.app n PUnit.unit⟩

lemma identityAt_reverse (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (x : C.Obj) :
    reverseArrow (underlyingGraph C) n (unitToArrow _ n (unitDatum C x)) =
      unitToArrow _ n (unitDatum C x) := by
  exact congrArg (fun a ↦ (⟨x, x, a⟩ : ArrowTotal (underlyingGraph C) n))
    (DaggerSimplicialStructure.dagger_id_app x n)

lemma quotientIdentityAt_total (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (x : Q.Obj) :
    (⟨x, x, quotientIdentityAt s n x⟩ : ArrowTotal Q n) =
      arrowMap π n (unitToArrow _ n (unitDatum B (s.rightSection.obj x))) :=
  congrArg (unitToArrow Q n) (quotientId_total s x)

lemma quotientIdentityAt_reverse (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (x : Q.Obj) :
    reverseArrow Q n ⟨x, x, quotientIdentityAt s n x⟩ = ⟨x, x, quotientIdentityAt s n x⟩ := by
  calc
    _ = reverseArrow Q n
        (arrowMap π n (unitToArrow _ n (unitDatum B (s.rightSection.obj x)))) := by
          rw [quotientIdentityAt_total]
    _ = arrowMap π n (reverseArrow (underlyingGraph B) n
        (unitToArrow _ n (unitDatum B (s.rightSection.obj x)))) := reverseArrow_map _ _ _
    _ = arrowMap π n (unitToArrow _ n (unitDatum B (s.rightSection.obj x))) := by
          rw [identityAt_reverse]
    _ = _ := (quotientIdentityAt_total s n x).symm

lemma compDatum_reverse (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (p : PairTotal (underlyingGraph C) n) :
    reverseArrow (underlyingGraph C) n (compDatum C n p) =
      compDatum C n (reversePair (underlyingGraph C) n p) := by
  rcases p with ⟨x, y, z, e₁, e₂⟩
  exact congrArg (fun a ↦ (⟨z, x, a⟩ : ArrowTotal (underlyingGraph C) n))
    (DaggerSimplicialStructure.dagger_comp_app (show C.Obj from x) y z n e₁ e₂)

lemma quotientCompDatum_reverse (s : GraphSplitData f g π) (n : SimplexCategoryᵒᵖ)
    (p : PairTotal Q n) :
    reverseArrow Q n (quotientCompDatum s n p) =
      quotientCompDatum s n (reversePair Q n p) := by
  calc
    _ = reverseArrow Q n (arrowMap π n (compDatum B n (pairMap s.rightSection n p))) := by
          rw [quotientComp_total]
    _ = arrowMap π n (reverseArrow (underlyingGraph B) n
        (compDatum B n (pairMap s.rightSection n p))) := reverseArrow_map _ _ _
    _ = arrowMap π n (compDatum B n
        (pairMap s.rightSection n (reversePair Q n p))) := by
          rw [compDatum_reverse, reversePair_map]
    _ = _ := (quotientComp_total s n (reversePair Q n p)).symm

/-- The quotient uses precisely the given simplicial graph dagger. -/
def quotientDaggerStructure (s : GraphSplitData f g π) :
    @DaggerSimplicialStructure Q.Obj (quotientEnrichedCategory s) := by
  letI : EnrichedCategory SSet.{u} Q.Obj := quotientEnrichedCategory s
  exact
    { dagger := Q.dagger
      dagger_involutive := Q.dagger_involutive
      dagger_id x := by
        apply NatTrans.ext
        funext n e
        cases e
        exact arrow_value_eq (quotientIdentityAt_reverse s n x)
      dagger_comp x y z := by
        apply NatTrans.ext
        funext n e
        rcases e with ⟨e₁, e₂⟩
        have h := arrow_value_eq (quotientCompDatum_reverse s n ⟨x, y, z, e₁, e₂⟩)
        simpa only [SSet.comp_app, Function.comp_apply, SSet.tensorHom_app_apply,
          sSetBraiding_app_apply] using h }

/-- Bundle the original quotient graph with its proved enriched and dagger laws. -/
def quotientCategory (s : GraphSplitData f g π) : DaggerSimplicialCat.{u, u} where
  toSimplicialCat := ⟨Q.Obj, quotientEnrichedCategory s⟩
  daggerStructure := quotientDaggerStructure s

@[simp] lemma underlyingGraph_quotientCategory (s : GraphSplitData f g π) :
    underlyingGraph (quotientCategory s) = Q := rfl

/-- The given quotient graph map is an actual dagger enriched functor. -/
def quotientFunctor (s : GraphSplitData f g π) : B ⟶ quotientCategory s where
  obj := π.obj
  map := π.map
  map_id := quotientId_preservation s
  map_comp := quotientComp_preservation s
  map_dagger := π.map_dagger

@[simp] lemma underlyingGraphMap_quotientFunctor (s : GraphSplitData f g π) :
    underlyingGraphMap (quotientFunctor s) = π := rfl

end DaggerModels.DaggerSimplicialCat.SplitCoequalizer
