import DaggerModels.SmallObjectFiniteDomains
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import NativeBoundaryJoyalMappingWeak

/-!
# Actual functorial inner-horn factorizations and quasi-category replacements

The family and lifting criterion follow Mathlib's later InnerFibration implementation
at commit fcd79238d34137c492bb55aef27aba0916e0a36f (Jack McKoen), adapted to the
existing dependency pin and its finite-domain small-object helper. The generators,
all simplicial operators, and the native Quasicategory class are retained.
The inner-left factor is proved native Kan trivial cofibrant; its Joyal mapping
weakness is a distinct remaining statement, not inferred from Kan weakness.
-/
set_option autoImplicit false
open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra
open DaggerModels
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeInnerHornFactorization
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] SmallObjectFiniteDomains.aleph0OrdOrderBot

/-- All original inner horns, with their original dimension and inner index. -/
def Index : Type := Σ n : ℕ, {i : Fin (n + 3) // 0 < i ∧ i < Fin.last (n + 2)}

def generator (a : Index) : (SSet.horn.{u} (a.1 + 2) a.2.1).toSSet ⟶ Δ[a.1 + 2] :=
  (SSet.horn (a.1 + 2) a.2.1).ι

def generators : MorphismProperty SSet.{u} := ofHoms generator

def innerFibrations : MorphismProperty SSet.{u} := generators.rlp

def innerAnodyne : MorphismProperty SSet.{u} := generators.rlp.llp

instance generatorsSmall : IsSmall.{u} generators.{u} := isSmall_ofHoms _

/-- The domains of the literal inner-horn family are finitely presentable. -/
theorem generators_domain_finitePresentable {A B : SSet.{u}} (i : A ⟶ B)
    (hi : generators i) : IsFinitelyPresentable.{u} A := by
  obtain ⟨a⟩ := hi
  infer_instance

instance generatorsCardinal : generators.{u}.IsCardinalForSmallObjectArgument
    Cardinal.aleph0.{u} :=
  SmallObjectFiniteDomains.isCardinalForSmallObjectArgument_aleph0.{u} _
    (fun i hi ↦ generators_domain_finitePresentable i hi)

instance generatorsSmallObject : HasSmallObjectArgument.{u} generators.{u} :=
  SmallObjectFiniteDomains.hasSmallObjectArgument.{u} _
    (fun i hi ↦ generators_domain_finitePresentable i hi)

/-- Full native inner-horn factorization of every actual map, with no model input. -/
def factorization : innerAnodyne.{u}.FunctorialFactorizationData innerFibrations.{u} :=
  SmallObject.functorialFactorizationData generators Cardinal.aleph0.{u}

instance hasFunctorialFactorization :
    innerAnodyne.{u}.HasFunctorialFactorization innerFibrations.{u} := ⟨⟨factorization⟩⟩

/-- The whole inner lifting class is exactly all original inner-horn tests. -/
theorem innerFibrations_iff {X Y : SSet.{u}} (p : X ⟶ Y) :
    innerFibrations p ↔ ∀ (n : ℕ) (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
      HasLiftingProperty (SSet.horn (n + 2) i).ι p := by
  constructor
  · intro hp n i h0 hn
    apply hp (generator ⟨n, ⟨i, h0, hn⟩⟩)
    exact ofHoms.mk _
  · intro hp A B i hi
    obtain ⟨a⟩ := hi
    exact hp a.1 a.2.1 a.2.2.1 a.2.2.2

/-- The actual native quasi-category condition is exactly the inner right class to a terminal. -/
theorem quasicategory_iff_inner_terminal {X T : SSet.{u}} (p : X ⟶ T)
    (hT : IsTerminal T) : X.Quasicategory ↔ innerFibrations p := by
  rw [innerFibrations_iff]
  constructor
  · intro h n i h0 hn
    haveI := h
    constructor
    intro f g sq
    obtain ⟨l, hl⟩ := SSet.Quasicategory.hornFilling h0 hn f
    exact ⟨l, hl.symm, hT.hom_ext _ _⟩
  · intro hp
    constructor
    intro n i f h0 hn
    haveI := hp n i h0 hn
    let sq : CommSq f (SSet.horn (n + 2) i).ι p (hT.from Δ[n + 2]) :=
      ⟨hT.hom_ext _ _⟩
    exact ⟨sq.lift, sq.fac_left.symm⟩

/-- Each inner horn is a trivial cofibration only in the already verified native Kan model. -/
theorem generators_le_native_trivial : generators.{u} ≤ trivialCofibrations SSet.{u} := by
  intro A B i hi
  obtain ⟨a⟩ := hi
  rw [← llp_eq_of_wfs (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
  intro X Y p hp
  haveI : Fibration p := (fibration_iff p).2 hp
  change HasLiftingProperty (SSet.horn (a.1 + 2) a.2.1).ι p
  infer_instance

/-- Every full inner-left map is native Kan trivial cofibrant. This is not a Joyal claim. -/
theorem innerAnodyne_le_native_trivial :
    innerAnodyne.{u} ≤ trivialCofibrations SSet.{u} := by
  have h := antitone_llp (antitone_rlp generators_le_native_trivial.{u})
  rw [rlp_eq_of_wfs (trivialCofibrations SSet.{u}) (fibrations SSet.{u}),
    llp_eq_of_wfs (trivialCofibrations SSet.{u}) (fibrations SSet.{u})] at h
  exact h

/-- The exact same inner-left factor is a monomorphism in every simplicial degree. -/
theorem innerAnodyne_mono {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i) : Mono i := by
  haveI : Cofibration i := ((mem_trivialCofibrations_iff i).1
    (innerAnodyne_le_native_trivial i hi)).1
  infer_instance

/-- The entire terminal-arrow functor used by the actual functorial replacement. -/
def terminalArrow : SSet.{u} ⥤ Arrow SSet.{u} where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _) (terminalIsTerminal.hom_ext _ _)

/-- Quasi-category replacement of every actual simplicial set and its full functorial action. -/
def replacement : SSet.{u} ⥤ SSet.{u} := terminalArrow ⋙ factorization.Z

/-- The unit is the literal inner-left factor of the original terminal arrow. -/
def unit : 𝟭 SSet.{u} ⟶ replacement.{u} where
  app X := factorization.i.app (terminalArrow.obj X)
  naturality _X _Y f := factorization.i.naturality (terminalArrow.map f)

/-- The replacement is a native quasi-category, for every input and universe. -/
instance replacement_quasicategory (X : SSet.{u}) : (replacement.obj X).Quasicategory :=
  (quasicategory_iff_inner_terminal (factorization.p.app (terminalArrow.obj X))
    terminalIsTerminal).2 (factorization.hp _)

/-- The actual replacement unit is inner-left; mapping weakness remains to be proved. -/
theorem unit_innerAnodyne (X : SSet.{u}) : innerAnodyne (unit.app X) := factorization.hi _

/-- The actual replacement unit is a monomorphism in every degree. -/
theorem unit_mono (X : SSet.{u}) : Mono (unit.app X) :=
  innerAnodyne_mono _ (unit_innerAnodyne X)

end
end DaggerNativeInnerHornFactorization
