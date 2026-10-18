import ChosenNecklaceJointImages

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

/-- Full unflanked flags. All joints belong to the first set; the last set is unrestricted. -/
structure Flag (T : NecklaceCode) (n : ℕ) : Type u where
  chain : Fin (n + 1) →o Set (Vertices.{u} T)
  joints : ∀ v : Vertices.{u} T, v.down ∈ T.joints → v ∈ chain 0

namespace Flag

variable {T U V : NecklaceCode} {n k l : ℕ}

@[ext] theorem ext {F G : Flag.{u} T n} (h : ∀ i, F.chain i = G.chain i) : F = G := by
  have hh : F.chain = G.chain := DFunLike.ext _ _ h
  cases F
  cases G
  cases hh
  rfl

def restrict (α : Fin (k + 1) →o Fin (n + 1)) (F : Flag.{u} T n) : Flag.{u} T k where
  chain := F.chain.comp α
  joints v hv := F.chain.monotone (Fin.zero_le (α 0)) (F.joints v hv)

def map (f : Hom.{u} T U) (F : Flag.{u} T n) : Flag.{u} U n where
  chain :=
    { toFun i := mapVertices f.map '' F.chain i
      monotone' i j h := Set.image_mono (F.chain.monotone h) }
  joints v hv := by
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (joints_subset_image f hv)
    refine ⟨ULift.up w, F.joints _ hw, ?_⟩
    apply ULift.ext
    exact he

theorem restrict_map (α : Fin (k + 1) →o Fin (n + 1))
    (f : Hom.{u} T U) (F : Flag.{u} T n) :
    restrict α (map f F) = map f (restrict α F) := ext (fun _ ↦ rfl)

theorem map_id (F : Flag.{u} T n) : map (Hom.id T) F = F := by
  apply ext
  intro i
  change mapVertices (𝟙 _) '' F.chain i = F.chain i
  rw [mapVertices_id, Set.image_id]

theorem map_comp (f : Hom.{u} T U) (g : Hom.{u} U V) (F : Flag.{u} T n) :
    map (Hom.comp f g) F = map g (map f F) := by
  apply ext
  intro i
  change mapVertices (f.map ≫ g.map) '' F.chain i =
    mapVertices g.map '' (mapVertices f.map '' F.chain i)
  rw [mapVertices_comp, Set.image_image]
  rfl

end Flag

def flagSSet (T : NecklaceCode) : SSet.{u} where
  obj q := Flag.{u} T q.unop.len
  map α := Flag.restrict α.unop.toOrderHom
  map_id q := by
    funext F
    exact Flag.ext (fun _ ↦ rfl)
  map_comp α β := by
    funext F
    exact Flag.ext (fun _ ↦ rfl)

def flagMap {T U : NecklaceCode} (f : Hom.{u} T U) : flagSSet.{u} T ⟶ flagSSet.{u} U where
  app _ := Flag.map f
  naturality _ _ α := by
    funext F
    exact (Flag.restrict_map α.unop.toOrderHom f F).symm

def flagFunctor : NecklaceCode ⥤ SSet.{u} where
  obj := flagSSet
  map := flagMap
  map_id T := by
    ext q F
    exact Flag.map_id F
  map_comp f g := by
    ext q F
    exact Flag.map_comp f g F

end

end DaggerChosenRigidificationNecklace.NecklaceCode
