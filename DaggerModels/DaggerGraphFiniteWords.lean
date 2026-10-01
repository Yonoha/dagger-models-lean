import DaggerModels.FreeSimplicialPaths
import DaggerModels.FreeSimplicialLift
import DaggerModels.DaggerGraphTotalSpace

/-!
# Finite composable words in dagger simplicial graphs

Length zero consists exactly of vertices. Each successor length is the exact
fiber of the prefix target and the last edge source. These fibers are naturally
equivalent to the original finite paths of the specified length, with endpoints
preserved. This is the word decomposition used in Part I `bg.lem.presentable`.
-/

open CategoryTheory

universe u

namespace DaggerModels.DaggerGraphFiniteWords

open FreeSimplicialPaths
open DaggerSimplicialGraph.TotalSpace

/-- A type with its two endpoint functions. -/
structure EndpointSpace (V : Type u) where
  carrier : Type u
  source : carrier → V
  target : carrier → V

/-- Finite words are built by successive composability fibers of actual edges. -/
def stage (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    ℕ → EndpointSpace G.Obj
  | 0 => ⟨G.Obj, id, id⟩
  | k + 1 =>
      { carrier := {q : (stage G n k).carrier × (edges G).obj n //
          (stage G n k).target q.1 = q.2.1}
        source := fun q ↦ (stage G n k).source q.val.1
        target := fun q ↦ q.val.2.2.1 }

abbrev Word (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) (k : ℕ) : Type u :=
  (stage G n k).carrier

/-- A finite word gives a path with precisely its recorded endpoints. -/
def toPath (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    (k : ℕ) → (w : Word G n k) → Path G n ((stage G n k).source w)
      ((stage G n k).target w) := by
  intro k
  induction k with
  | zero => intro w; exact .nil
  | succ k ih =>
    rintro ⟨⟨w, x, y, e⟩, hx⟩
    change (stage G n k).target w = x at hx
    subst x
    exact (ih w).cons e

theorem toPath_length (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (k : ℕ) (w : Word G n k) : (toPath G n k w).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases w with ⟨⟨w, x, y, e⟩, hx⟩
    change (stage G n k).target w = x at hx
    subst x
    change (toPath G n k w).length + 1 = k + 1
    rw [ih]

/-- Decompose an actual path of specified length, preserving both endpoints. -/
def fromPath (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) :
    (k : ℕ) → {x y : G.Obj} → (p : Path G n x y) → (h : p.length = k) →
      {w : Word G n k // (stage G n k).source w = x ∧ (stage G n k).target w = y} := by
  letI := quiverAt G n
  intro k
  induction k with
  | zero =>
    intro x y p hp
    cases p with
    | nil => exact ⟨x, rfl, rfl⟩
    | cons p e => simp [Quiver.Path.length] at hp
  | succ k ih =>
    intro x z p hp
    cases p with
    | nil => simp [Quiver.Path.length] at hp
    | @cons y z p e =>
      have h : p.length = k := Nat.succ.inj hp
      let w := ih p h
      exact ⟨⟨⟨w.val, y, z, e⟩, w.property.2⟩, w.property.1, rfl⟩

theorem fromPath_toPath (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (k : ℕ) (w : Word G n k) :
    (fromPath G n k (toPath G n k w) (toPath_length G n k w)).val = w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases w with ⟨⟨w, x, y, e⟩, hx⟩
    change (stage G n k).target w = x at hx
    subst x
    apply Subtype.ext
    change ((fromPath G n k (toPath G n k w) _).val,
      (⟨_, y, e⟩ : (edges G).obj n)) = (w, (⟨_, y, e⟩ : (edges G).obj n))
    rw [ih]

theorem toPath_fromPath (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (k : ℕ) {x y : G.Obj} (p : Path G n x y) (hp : p.length = k) :
    HEq (toPath G n k (fromPath G n k p hp).val) p := by
  letI := quiverAt G n
  induction k generalizing x y with
  | zero =>
    cases p with
    | nil => rfl
    | cons p e => simp [Quiver.Path.length] at hp
  | succ k ih =>
    cases p with
    | nil => simp [Quiver.Path.length] at hp
    | @cons y z p e =>
      rename_i z
      have h : p.length = k := Nat.succ.inj hp
      have ihp := ih p h
      change HEq (toPath G n (k + 1)
        ⟨⟨(fromPath G n k p h).val, y, z, e⟩, (fromPath G n k p h).property.2⟩) (p.cons e)
      generalize hw : fromPath G n k p h = w at ihp ⊢
      rcases w with ⟨w, hx, hy⟩
      subst x
      subst y
      change HEq ((toPath G n k w).cons e) (p.cons e)
      exact heq_of_eq (congrArg (fun q ↦ q.cons e) (eq_of_heq ihp))

/-- Actual paths of length `k`, retaining their two endpoint labels. -/
abbrev LengthPath (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) (k : ℕ) : Type u :=
  Σ x : G.Obj, Σ y : G.Obj, {p : Path G n x y // p.length = k}

/-- Recursive composability fibers are exactly the actual paths of each length. -/
def wordPathEquiv (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ) (k : ℕ) :
    Word G n k ≃ LengthPath G n k where
  toFun w := ⟨(stage G n k).source w, (stage G n k).target w,
    toPath G n k w, toPath_length G n k w⟩
  invFun p := (fromPath G n k p.2.2.val p.2.2.property).val
  left_inv w := fromPath_toPath G n k w
  right_inv q := by
    rcases q with ⟨x, y, p, hp⟩
    dsimp only
    have h := toPath_fromPath G n k p hp
    generalize hw : fromPath G n k p hp = w at h ⊢
    rcases w with ⟨w, hx, hy⟩
    subst x
    subst y
    refine Sigma.ext ?_ ?_
    · rfl
    · apply heq_of_eq
      refine Sigma.ext ?_ ?_
      · rfl
      · exact heq_of_eq (Subtype.ext (eq_of_heq h))

@[simp] theorem wordPathEquiv_source (G : DaggerSimplicialGraph.{u})
    (n : SimplexCategoryᵒᵖ) (k : ℕ) (w : Word G n k) :
    (wordPathEquiv G n k w).1 = (stage G n k).source w := rfl

@[simp] theorem wordPathEquiv_target (G : DaggerSimplicialGraph.{u})
    (n : SimplexCategoryᵒᵖ) (k : ℕ) (w : Word G n k) :
    (wordPathEquiv G n k w).2.1 = (stage G n k).target w := rfl

@[simp] theorem wordPathEquiv_zero (G : DaggerSimplicialGraph.{u})
    (n : SimplexCategoryᵒᵖ) (x : G.Obj) :
    wordPathEquiv G n 0 x = ⟨x, x, Quiver.Path.nil, rfl⟩ := rfl

/-- A map of endpoint spaces lying over an arbitrary map of vertices. -/
structure EndpointMap {V W : Type u} (f : V → W)
    (A : EndpointSpace V) (B : EndpointSpace W) where
  map : A.carrier → B.carrier
  source : ∀ w, B.source (map w) = f (A.source w)
  target : ∀ w, B.target (map w) = f (A.target w)

variable (G H : DaggerSimplicialGraph.{u}) (n m : SimplexCategoryᵒᵖ)
  (f : G.Obj → H.Obj) (φ : ∀ x y, (G.Hom x y).obj n → (H.Hom (f x) (f y)).obj m)

/-- Apply a vertex map and its edge assignment to each finite composability fiber. -/
def stageMap : (k : ℕ) → EndpointMap f (stage G n k) (stage H m k)
  | 0 => ⟨f, fun _ ↦ rfl, fun _ ↦ rfl⟩
  | k + 1 =>
      { map := fun w ↦
          ⟨⟨(stageMap k).map w.val.1,
            ⟨f w.val.2.1, f w.val.2.2.1, φ w.val.2.1 w.val.2.2.1 w.val.2.2.2⟩⟩,
            ((stageMap k).target w.val.1).trans (congrArg f w.property)⟩
        source := fun w ↦ (stageMap k).source w.val.1
        target := fun _ ↦ rfl }

/-- The same edge assignment as an actual map of degreewise quivers. -/
def quiverMap : At G n ⥤q At H m where
  obj := f
  map {x y} e := φ x y e

theorem mapPath_length {x y : G.Obj} (p : Path G n x y) :
    ((quiverMap G H n m f φ).mapPath p).length = p.length := by
  letI := quiverAt G n
  induction p with
  | nil => rfl
  | cons p e ih =>
    change ((quiverMap G H n m f φ).mapPath p).length + 1 = p.length + 1
    rw [ih]

/-- Decomposing paths commutes with arbitrary vertex and edge assignments. -/
theorem fromPath_mapPath (k : ℕ) {x y : G.Obj} (p : Path G n x y) (hp : p.length = k) :
    (stageMap G H n m f φ k).map (fromPath G n k p hp).val =
      (fromPath H m k ((quiverMap G H n m f φ).mapPath p)
        ((mapPath_length G H n m f φ p).trans hp)).val := by
  letI := quiverAt G n
  induction k generalizing x y with
  | zero =>
    cases p with
    | nil => rfl
    | cons p e => simp [Quiver.Path.length] at hp
  | succ k ih =>
    cases p with
    | nil => simp [Quiver.Path.length] at hp
    | @cons y z p e =>
      apply Subtype.ext
      apply Prod.ext
      · change (stageMap G H n m f φ k).map (fromPath G n k p _).val =
          (fromPath H m k ((quiverMap G H n m f φ).mapPath p) _).val
        exact ih p (Nat.succ.inj hp)
      · rfl

/-- The pointwise action on actual paths of fixed length retains endpoint labels. -/
def lengthPathMap (k : ℕ) (p : LengthPath G n k) : LengthPath H m k :=
  ⟨f p.1, f p.2.1, (quiverMap G H n m f φ).mapPath p.2.2.val,
    (mapPath_length G H n m f φ p.2.2.val).trans p.2.2.property⟩

/-- The exact-length equivalence is natural for arbitrary maps of vertices and edges. -/
theorem wordPathEquiv_naturality (k : ℕ) (w : Word G n k) :
    wordPathEquiv H m k ((stageMap G H n m f φ k).map w) =
      lengthPathMap G H n m f φ k (wordPathEquiv G n k w) := by
  apply (wordPathEquiv H m k).symm.injective
  rw [Equiv.symm_apply_apply]
  change (stageMap G H n m f φ k).map w =
    (fromPath H m k ((quiverMap G H n m f φ).mapPath (toPath G n k w)) _).val
  conv_lhs => rw [← fromPath_toPath G n k w]
  exact fromPath_mapPath G H n m f φ k (toPath G n k w) (toPath_length G n k w)

/-- A graph map acts on every vertex and edge of a finite word. -/
def graphMap {G H : DaggerSimplicialGraph.{u}} (a : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) (k : ℕ) : Word G n k → Word H n k :=
  (stageMap G H n n a.obj (fun x y ↦ (a.map x y).app n) k).map

theorem graphMap_source {G H : DaggerSimplicialGraph.{u}} (a : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) (k : ℕ) (w : Word G n k) :
    (stage H n k).source (graphMap a n k w) = a.obj ((stage G n k).source w) :=
  (stageMap G H n n a.obj (fun x y ↦ (a.map x y).app n) k).source w

theorem graphMap_target {G H : DaggerSimplicialGraph.{u}} (a : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) (k : ℕ) (w : Word G n k) :
    (stage H n k).target (graphMap a n k w) = a.obj ((stage G n k).target w) :=
  (stageMap G H n n a.obj (fun x y ↦ (a.map x y).app n) k).target w

@[simp] theorem graphMap_id (G : DaggerSimplicialGraph.{u}) (n : SimplexCategoryᵒᵖ)
    (k : ℕ) (w : Word G n k) : graphMap (𝟙 G) n k w = w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply Subtype.ext
    apply Prod.ext
    · exact ih w.val.1
    · rfl

@[simp] theorem graphMap_comp {G H K : DaggerSimplicialGraph.{u}}
    (a : G ⟶ H) (b : H ⟶ K) (n : SimplexCategoryᵒᵖ) (k : ℕ) (w : Word G n k) :
    graphMap (a ≫ b) n k w = graphMap b n k (graphMap a n k w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply Subtype.ext
    apply Prod.ext
    · exact ih w.val.1
    · rfl

theorem wordPathEquiv_graphMap {G H : DaggerSimplicialGraph.{u}} (a : G ⟶ H)
    (n : SimplexCategoryᵒᵖ) (k : ℕ) (w : Word G n k) :
    wordPathEquiv H n k (graphMap a n k w) =
      lengthPathMap G H n n a.obj (fun x y ↦ (a.map x y).app n) k
        (wordPathEquiv G n k w) :=
  wordPathEquiv_naturality G H n n a.obj (fun x y ↦ (a.map x y).app n) k w

/-- Apply an ordinary simplex operator to every edge of the finite tuple. -/
def simplexMap (G : DaggerSimplicialGraph.{u}) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (k : ℕ) : Word G n k → Word G m k :=
  (stageMap G G n m id (fun x y ↦ (G.Hom x y).map α) k).map

theorem quiverMap_simplex (G : DaggerSimplicialGraph.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    quiverMap G G n m id (fun x y ↦ (G.Hom x y).map α) = operator G α := rfl

theorem wordPathEquiv_simplexMap (G : DaggerSimplicialGraph.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (k : ℕ) (w : Word G n k) :
    wordPathEquiv G m k (simplexMap G α k w) =
      lengthPathMap G G n m id (fun x y ↦ (G.Hom x y).map α) k
        (wordPathEquiv G n k w) :=
  wordPathEquiv_naturality G G n m id (fun x y ↦ (G.Hom x y).map α) k w

end DaggerModels.DaggerGraphFiniteWords
