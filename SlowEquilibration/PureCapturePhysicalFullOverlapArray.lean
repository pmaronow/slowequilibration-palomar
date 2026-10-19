-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalScoreTightness
public import SlowEquilibration.GaussianReplicaKernel
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! The finite full overlap arrays of ordinary disorder-averaged Gibbs
replicas. These retain cross-block overlaps that the capture score forgets;
their compact weak limits are the input space for Dovbysh--Sudakov. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFullOverlapArray

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open SphericalAging.HardSphereDynamics
open SphericalBarycenter
open PureCapturePhysicalScoreTightness
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

abbrev FullOverlapCoordinates (m : ℕ) := Fin m → Fin m → ℝ

/-- The diagonal of a Gram overlap array is fixed at one, including for
off-sphere inputs. This agrees with the physical spherical law a.e. -/
def physicalFullOverlapCoordinates {N m : ℕ}
    (σ : Fin m → Vector N) : FullOverlapCoordinates m :=
  fun i j => if i = j then 1 else overlap (σ i) (σ j)

theorem physicalFullOverlapCoordinates_continuous {N m : ℕ} :
    Continuous (physicalFullOverlapCoordinates (N := N) (m := m)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · simpa [physicalFullOverlapCoordinates, hij] using
      (continuous_const : Continuous (fun _ : Fin m → Vector N => (1 : ℝ)))
  · have hpair : Continuous (fun σ : Fin m → Vector N => (σ i, σ j)) :=
      (continuous_apply i).prodMk (continuous_apply j)
    simpa only [physicalFullOverlapCoordinates, hij, ite_false, Function.comp_def,
      Prod.fst, Prod.snd] using
      (PureCapturePhysicalFiniteMeasurability.overlap_joint_continuous.comp hpair)

def physicalReplicaLaw {n m : ℕ} (μ : FiniteMixture) (β : ℝ) :
    Measure (Fin m → Vector (n+2)) :=
  GaussianReplicaKernel.law (disorderLaw (n+2) μ.maxDegree)
    (allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β) m

instance physicalReplicaLaw_probability {n m : ℕ} (μ : FiniteMixture) (β : ℝ) :
    IsProbabilityMeasure (physicalReplicaLaw (n := n) (m := m) μ β) := by
  unfold physicalReplicaLaw
  infer_instance

def physicalFullOverlapLaw {n m : ℕ} (μ : FiniteMixture) (β : ℝ) :
    ProbabilityMeasure (FullOverlapCoordinates m) :=
  ((physicalReplicaLaw (n := n) (m := m) μ β).toProbabilityMeasure).map
    physicalFullOverlapCoordinates

/-- The full physical overlap-array law has exact projective consistency. -/
def fullOverlapPrefix {m : ℕ} (c : FullOverlapCoordinates (m+1)) :
    FullOverlapCoordinates m :=
  fun i j => c i.castSucc j.castSucc

theorem fullOverlapPrefix_continuous {m : ℕ} :
    Continuous (fullOverlapPrefix (m := m)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply j.castSucc).comp (continuous_apply i.castSucc)

theorem fullOverlapPrefix_physical {N m : ℕ}
    (σ : Fin (m+1) → Vector N) :
    fullOverlapPrefix (physicalFullOverlapCoordinates σ) =
      physicalFullOverlapCoordinates (GaussianReplicaKernel.initial σ) := by
  ext i j
  simp [fullOverlapPrefix, physicalFullOverlapCoordinates, GaussianReplicaKernel.initial]

theorem physicalFullOverlapLaw_map_prefix {n m : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    (physicalFullOverlapLaw (n := n) (m := m+1) μ β).map fullOverlapPrefix =
      physicalFullOverlapLaw (n := n) (m := m) μ β := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((physicalReplicaLaw (n := n) (m := m+1) μ β).map
      physicalFullOverlapCoordinates).map fullOverlapPrefix =
    (physicalReplicaLaw (n := n) (m := m) μ β).map physicalFullOverlapCoordinates
  rw [Measure.map_map fullOverlapPrefix_continuous.measurable
    physicalFullOverlapCoordinates_continuous.measurable]
  simp only [Function.comp_def, fullOverlapPrefix_physical]
  change Measure.map (physicalFullOverlapCoordinates ∘ GaussianReplicaKernel.initial)
      (physicalReplicaLaw (n := n) (m := m+1) μ β) = _
  rw [← Measure.map_map physicalFullOverlapCoordinates_continuous.measurable
    (GaussianReplicaKernel.initial_measurable m)]
  exact congrArg (fun ρ : Measure (Fin m → Vector (n+2)) =>
      ρ.map physicalFullOverlapCoordinates)
    ((GaussianReplicaKernel.initial_hasLaw
      (disorderLaw (n+2) μ.maxDegree)
      (allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β) m).map_eq)

def replicasOnSphere {N m : ℕ} : Set (Fin m → Vector N) :=
  {σ | ∀ i, OnSphere (σ i)}

theorem replicasOnSphere_measurable {N m : ℕ} :
    MeasurableSet (replicasOnSphere (N := N) (m := m)) := by
  have hS : MeasurableSet {x : Vector N | OnSphere x} := by
    have hclosed : IsClosed {x : Vector N | ‖x‖ ^ 2 = (N : ℝ)} :=
      isClosed_eq (continuous_norm.pow 2) continuous_const
    convert hclosed.measurableSet using 1
    ext x
    exact onSphere_iff_norm_sq x
  unfold replicasOnSphere
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => hS.preimage (measurable_pi_apply i))

theorem physicalReplicaLaw_sphere_ae {n m : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ σ ∂physicalReplicaLaw (n := n) (m := m) μ β,
      σ ∈ replicasOnSphere := by
  apply mem_ae_iff.mpr
  unfold physicalReplicaLaw GaussianReplicaKernel.law
  change ((disorderLaw (n+2) μ.maxDegree).bind
    (GaussianReplicaKernel.iid
      (allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β) m))
        (replicasOnSphere (N := n+2) (m := m))ᶜ = 0
  rw [Measure.bind_apply replicasOnSphere_measurable.compl
    (GaussianReplicaKernel.iid
      (allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β) m).aemeasurable]
  have hzero (J : Disorder (n+2) μ.maxDegree) :
      (GaussianReplicaKernel.iid
        (allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β) m J)
        (replicasOnSphere (N := n+2) (m := m))ᶜ = 0 := by
    rw [GaussianReplicaKernel.iid_apply, allDimensionGibbsKernel_apply]
    let π := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)
    let : IsProbabilityMeasure π :=
      gibbsLaw_probability (by omega) β
        (field_contDiff (mixtureCoefficients μ) J).continuous
    have hπ : ∀ᵐ x ∂π, OnSphere x :=
      (gibbsLaw_support (by omega) β
        (field (mixtureCoefficients μ) J)).mono
          (fun x hx => (onSphere_iff_norm_sq x).mpr hx)
    have hσ : ∀ᵐ σ ∂Measure.pi (fun _ : Fin m => π),
        ∀ i : Fin m, OnSphere (σ i) :=
      Filter.eventually_all.mpr (fun i =>
        (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => π) (i := i)).eventually hπ)
    exact mem_ae_iff.mp hσ
  have hfun : (fun J : Disorder (n+2) μ.maxDegree =>
      (GaussianReplicaKernel.iid
        (allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β) m J)
          (replicasOnSphere (N := n+2) (m := m))ᶜ) =
      (fun _ => 0) := funext hzero
  rw [hfun]
  simp

def fullOverlapCube (m : ℕ) : Set (FullOverlapCoordinates m) :=
  Set.pi univ (fun _ : Fin m => Set.pi univ (fun _ : Fin m => Icc (-1 : ℝ) 1))

theorem fullOverlapCube_compact (m : ℕ) : IsCompact (fullOverlapCube m) := by
  unfold fullOverlapCube
  exact isCompact_univ_pi (fun _ : Fin m =>
    isCompact_univ_pi (fun _ : Fin m => isCompact_Icc))

theorem physicalFullOverlapCoordinates_mem_cube {n m : ℕ}
    {σ : Fin m → Vector (n+2)}
    (hσ : σ ∈ replicasOnSphere) :
    physicalFullOverlapCoordinates σ ∈ fullOverlapCube m := by
  change ∀ i : Fin m, i ∈ univ → ∀ j : Fin m, j ∈ univ →
    (if i = j then (1 : ℝ) else overlap (σ i) (σ j)) ∈ Icc (-1 : ℝ) 1
  intro i _ j _
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using
      (overlap_mem_Icc_of_norm_sq (by omega : 1 ≤ n+2) (σ i) (σ j)
        ((onSphere_iff_norm_sq (σ i)).mp (hσ i))
        ((onSphere_iff_norm_sq (σ j)).mp (hσ j)))

theorem physicalFullOverlapLaw_cube_ae {n m : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ c ∂(physicalFullOverlapLaw (n := n) (m := m) μ β :
      Measure (FullOverlapCoordinates m)), c ∈ fullOverlapCube m := by
  have hcube : MeasurableSet (fullOverlapCube m) :=
    (fullOverlapCube_compact m).isClosed.measurableSet
  unfold physicalFullOverlapLaw
  apply (ae_map_iff physicalFullOverlapCoordinates_continuous.measurable.aemeasurable hcube).2
  exact (physicalReplicaLaw_sphere_ae μ β).mono
    (fun σ hσ => physicalFullOverlapCoordinates_mem_cube hσ)

theorem physicalFullOverlapLaws_compact_closure {m : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    IsCompact (closure (Set.range (fun n : ℕ =>
      physicalFullOverlapLaw (n := n) (m := m) μ β))) := by
  apply isCompact_closure_of_isTightMeasureSet
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε _
  refine ⟨fullOverlapCube m, fullOverlapCube_compact m, ?_⟩
  intro ρ hρ
  obtain ⟨ν, ⟨n, rfl⟩, rfl⟩ := hρ
  have hzero : (physicalFullOverlapLaw (n := n) (m := m) μ β :
      Measure (FullOverlapCoordinates m)) (fullOverlapCube m)ᶜ = 0 :=
    mem_ae_iff.mp (physicalFullOverlapLaw_cube_ae μ β)
  rw [hzero]
  exact bot_le

/-- The actual physical finite arrays admit a common full-array weak
subsequence, retaining all cross-block overlaps. -/
abbrev FullOverlapLawArray :=
  (m : ℕ) → ProbabilityMeasure (FullOverlapCoordinates m)

def physicalFullOverlapLawArray (μ : FiniteMixture) (β : ℝ)
    (n : ℕ) : FullOverlapLawArray :=
  fun m => physicalFullOverlapLaw (n := n) (m := m) μ β

def physicalFullOverlapArrayLimitSet (μ : FiniteMixture)
    (β : ℝ) : Set FullOverlapLawArray :=
  closure (Set.range (physicalFullOverlapLawArray μ β))

theorem physicalFullOverlapArrayLimitSet_compact
    (μ : FiniteMixture) (β : ℝ) :
    IsCompact (physicalFullOverlapArrayLimitSet μ β) := by
  let C (m : ℕ) : Set (ProbabilityMeasure (FullOverlapCoordinates m)) :=
    closure (Set.range (fun n : ℕ =>
      physicalFullOverlapLaw (n := n) (m := m) μ β))
  have hC (m : ℕ) : IsCompact (C m) := physicalFullOverlapLaws_compact_closure μ β
  have hprod : IsCompact (Set.pi univ C) := isCompact_univ_pi hC
  have hrange : Set.range (physicalFullOverlapLawArray μ β) ⊆ Set.pi univ C := by
    intro x hx m _
    obtain ⟨n, rfl⟩ := hx
    exact subset_closure (Set.mem_range.mpr ⟨n, rfl⟩)
  exact hprod.closure_of_subset hrange

theorem physicalFullOverlapArrayLimitSet_tendsto_subseq
    (μ : FiniteMixture) (β : ℝ) (s : ℕ → ℕ) :
    ∃ limitArray ∈ physicalFullOverlapArrayLimitSet μ β,
      ∃ t : ℕ → ℕ, StrictMono t ∧
        Tendsto (fun j : ℕ => physicalFullOverlapLawArray μ β (s (t j)))
          atTop (𝓝 limitArray) := by
  apply (physicalFullOverlapArrayLimitSet_compact μ β).tendsto_subseq
    (x := fun j => physicalFullOverlapLawArray μ β (s j))
  intro j
  exact subset_closure (Set.mem_range.mpr ⟨s j, rfl⟩)

def consistentFullOverlapLawArrays : Set FullOverlapLawArray :=
  {x | ∀ m, (x (m+1)).map fullOverlapPrefix = x m}

theorem consistentFullOverlapLawArrays_closed :
    IsClosed consistentFullOverlapLawArrays := by
  unfold consistentFullOverlapLawArrays
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro m
  exact isClosed_eq
    ((ProbabilityMeasure.continuous_map fullOverlapPrefix_continuous).comp
      (continuous_apply (m+1)))
    (continuous_apply m)

theorem physicalFullOverlapLawArray_consistent
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) :
    physicalFullOverlapLawArray μ β n ∈ consistentFullOverlapLawArrays := by
  intro m
  exact physicalFullOverlapLaw_map_prefix μ β

theorem physicalFullOverlapArrayLimitSet_consistent
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray} (hx : x ∈ physicalFullOverlapArrayLimitSet μ β) :
    x ∈ consistentFullOverlapLawArrays := by
  apply closure_minimal _ consistentFullOverlapLawArrays_closed hx
  rintro x ⟨n, rfl⟩
  exact physicalFullOverlapLawArray_consistent μ β n

def fullGramCone (m : ℕ) : Set (FullOverlapCoordinates m) :=
  {c | Matrix.PosSemidef (Matrix.of c)}

theorem fullGramCone_closed (m : ℕ) : IsClosed (fullGramCone m) :=
  by
    have hcont : Continuous (fun c : FullOverlapCoordinates m => Matrix.of c) :=
      continuous_matrixOf.mpr continuous_id
    exact (Matrix.posSemidef_is_closed (n := Fin m) (𝕜 := ℝ)).preimage hcont

/-- Each actual on-sphere overlap array is a Gram matrix of normalized
physical spins. -/
theorem physicalFullOverlapCoordinates_mem_gram {n m : ℕ}
    {σ : Fin m → Vector (n+2)}
    (hσ : σ ∈ replicasOnSphere) :
    physicalFullOverlapCoordinates σ ∈ fullGramCone m := by
  have hmatrix : Matrix.of (physicalFullOverlapCoordinates σ) =
      Matrix.gram ℝ (fun i => spin (σ i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      change (if i = i then (1 : ℝ) else overlap (σ i) (σ i)) =
        inner ℝ (spin (σ i)) (spin (σ i))
      rw [spin_inner (by omega : 1 ≤ n+2)]
      simp only [ite_true]
      exact (overlap_self (by omega : 0 < n+2) (σ i)
        ((onSphere_iff_norm_sq (σ i)).mp (hσ i))).symm
    · change (if i = j then (1 : ℝ) else overlap (σ i) (σ j)) =
        inner ℝ (spin (σ i)) (spin (σ j))
      rw [spin_inner (by omega : 1 ≤ n+2)]
      simp only [hij, ite_false]
  change Matrix.PosSemidef (Matrix.of (physicalFullOverlapCoordinates σ))
  rw [hmatrix]
  exact Matrix.posSemidef_gram ℝ _

theorem physicalFullOverlapLaw_gram_ae {n m : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ c ∂(physicalFullOverlapLaw (n := n) (m := m) μ β :
      Measure (FullOverlapCoordinates m)), c ∈ fullGramCone m := by
  have hC : MeasurableSet (fullGramCone m) := (fullGramCone_closed m).measurableSet
  unfold physicalFullOverlapLaw
  apply (ae_map_iff physicalFullOverlapCoordinates_continuous.measurable.aemeasurable hC).2
  exact (physicalReplicaLaw_sphere_ae μ β).mono
    (fun σ hσ => physicalFullOverlapCoordinates_mem_gram hσ)

/-- Probability laws supported on a fixed closed finite-array constraint
form a closed subset of the weak topology. -/
theorem supportedProbabilityLaws_closed {m : ℕ}
    {C : Set (FullOverlapCoordinates m)} (hC : IsClosed C) :
    IsClosed {ρ : ProbabilityMeasure (FullOverlapCoordinates m) |
      ∀ᵐ c ∂(ρ : Measure (FullOverlapCoordinates m)), c ∈ C} := by
  let S : Set (ProbabilityMeasure (FullOverlapCoordinates m)) :=
    {ρ | ∀ᵐ c ∂(ρ : Measure (FullOverlapCoordinates m)), c ∈ C}
  change IsClosed S
  rw [← closure_eq_iff_isClosed]
  apply Set.Subset.antisymm
  · intro ρ hρ
    obtain ⟨ρs, hρs, hlim⟩ := mem_closure_iff_seq_limit.mp hρ
    have hopen := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      hlim hC.isOpen_compl
    have hzero (j : ℕ) :
        (ρs j : Measure (FullOverlapCoordinates m)) Cᶜ = 0 :=
      mem_ae_iff.mp (hρs j)
    have heq : (fun j => (ρs j : Measure (FullOverlapCoordinates m)) Cᶜ) =
        (fun _ => 0) := funext hzero
    rw [heq, Filter.liminf_const] at hopen
    exact mem_ae_iff.mpr (le_zero_iff.mp hopen)
  · exact subset_closure

def gramFullOverlapLawArrays : Set FullOverlapLawArray :=
  {x | ∀ m, ∀ᵐ c ∂(x m : Measure (FullOverlapCoordinates m)),
    c ∈ fullGramCone m}

theorem gramFullOverlapLawArrays_closed :
    IsClosed gramFullOverlapLawArrays := by
  unfold gramFullOverlapLawArrays
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro m
  have hcont : Continuous (fun x : FullOverlapLawArray => x m) := continuous_apply m
  exact IsClosed.preimage hcont
    (supportedProbabilityLaws_closed (m := m) (fullGramCone_closed m))

theorem physicalFullOverlapArrayLimitSet_gram
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray} (hx : x ∈ physicalFullOverlapArrayLimitSet μ β) :
    x ∈ gramFullOverlapLawArrays := by
  apply closure_minimal _ gramFullOverlapLawArrays_closed hx
  rintro x ⟨n, rfl⟩ m
  exact physicalFullOverlapLaw_gram_ae μ β

def fullUnitDiagonal (m : ℕ) : Set (FullOverlapCoordinates m) :=
  {c | ∀ i : Fin m, c i i = 1}

theorem fullUnitDiagonal_closed (m : ℕ) : IsClosed (fullUnitDiagonal m) := by
  unfold fullUnitDiagonal
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_eq
    ((continuous_apply i).comp (continuous_apply i)) continuous_const

theorem physicalFullOverlapCoordinates_mem_unitDiagonal {N m : ℕ}
    (σ : Fin m → Vector N) :
    physicalFullOverlapCoordinates σ ∈ fullUnitDiagonal m := by
  intro i
  simp [physicalFullOverlapCoordinates]

theorem physicalFullOverlapLaw_unitDiagonal_ae {n m : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ c ∂(physicalFullOverlapLaw (n := n) (m := m) μ β :
      Measure (FullOverlapCoordinates m)), c ∈ fullUnitDiagonal m := by
  have hC : MeasurableSet (fullUnitDiagonal m) :=
    (fullUnitDiagonal_closed m).measurableSet
  unfold physicalFullOverlapLaw
  apply (ae_map_iff physicalFullOverlapCoordinates_continuous.measurable.aemeasurable hC).2
  exact Filter.Eventually.of_forall physicalFullOverlapCoordinates_mem_unitDiagonal

def unitDiagonalFullOverlapLawArrays : Set FullOverlapLawArray :=
  {x | ∀ m, ∀ᵐ c ∂(x m : Measure (FullOverlapCoordinates m)),
    c ∈ fullUnitDiagonal m}

theorem unitDiagonalFullOverlapLawArrays_closed :
    IsClosed unitDiagonalFullOverlapLawArrays := by
  unfold unitDiagonalFullOverlapLawArrays
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro m
  have hcont : Continuous (fun x : FullOverlapLawArray => x m) := continuous_apply m
  exact IsClosed.preimage hcont
    (supportedProbabilityLaws_closed (m := m) (fullUnitDiagonal_closed m))

theorem physicalFullOverlapArrayLimitSet_unitDiagonal
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray} (hx : x ∈ physicalFullOverlapArrayLimitSet μ β) :
    x ∈ unitDiagonalFullOverlapLawArrays := by
  apply closure_minimal _ unitDiagonalFullOverlapLawArrays_closed hx
  rintro x ⟨n, rfl⟩ m
  exact physicalFullOverlapLaw_unitDiagonal_ae μ β

def permuteReplicas {N m : ℕ} (e : Equiv.Perm (Fin m))
    (σ : Fin m → Vector N) : Fin m → Vector N :=
  fun i => σ (e i)

theorem permuteReplicas_measurable {N m : ℕ} (e : Equiv.Perm (Fin m)) :
    Measurable (permuteReplicas (N := N) e) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply (e i)

def permuteFullOverlap {m : ℕ} (e : Equiv.Perm (Fin m))
    (c : FullOverlapCoordinates m) : FullOverlapCoordinates m :=
  fun i j => c (e i) (e j)

theorem permuteFullOverlap_continuous {m : ℕ} (e : Equiv.Perm (Fin m)) :
    Continuous (permuteFullOverlap e) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (e j)).comp (continuous_apply (e i))

theorem permuteFullOverlap_physical {N m : ℕ}
    (e : Equiv.Perm (Fin m)) (σ : Fin m → Vector N) :
    permuteFullOverlap e (physicalFullOverlapCoordinates σ) =
      physicalFullOverlapCoordinates (permuteReplicas e σ) := by
  ext i j
  simp [permuteFullOverlap, physicalFullOverlapCoordinates, permuteReplicas,
    e.injective.eq_iff]

theorem physicalReplicaLaw_permute {n m : ℕ}
    (μ : FiniteMixture) (β : ℝ) (e : Equiv.Perm (Fin m)) :
    (physicalReplicaLaw (n := n) (m := m) μ β).map
      (permuteReplicas e) = physicalReplicaLaw (n := n) (m := m) μ β := by
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  have hfun : (permuteReplicas (N := n+2) e) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin m => Vector (n+2)) e.symm) := by
    funext σ i
    simp [permuteReplicas, MeasurableEquiv.piCongrLeft,
      Equiv.piCongrLeft_apply]
  have hkernel : (GaussianReplicaKernel.iid G m).map (permuteReplicas e) =
      GaussianReplicaKernel.iid G m := by
    apply Kernel.ext
    intro J
    rw [Kernel.map_apply _ (permuteReplicas_measurable e),
      GaussianReplicaKernel.iid_apply]
    rw [hfun]
    exact (measurePreserving_piCongrLeft
      (α := fun _ : Fin m => Vector (n+2))
      (fun _ : Fin m => G J) e.symm).map_eq
  unfold physicalReplicaLaw GaussianReplicaKernel.law
  rw [Measure.map_comp _ _ (permuteReplicas_measurable e), hkernel]

theorem physicalFullOverlapLaw_permute {n m : ℕ}
    (μ : FiniteMixture) (β : ℝ) (e : Equiv.Perm (Fin m)) :
    (physicalFullOverlapLaw (n := n) (m := m) μ β).map
      (permuteFullOverlap e) = physicalFullOverlapLaw (n := n) (m := m) μ β := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((physicalReplicaLaw (n := n) (m := m) μ β).map
    physicalFullOverlapCoordinates).map (permuteFullOverlap e) =
    (physicalReplicaLaw (n := n) (m := m) μ β).map
      physicalFullOverlapCoordinates
  rw [Measure.map_map (permuteFullOverlap_continuous e).measurable
    physicalFullOverlapCoordinates_continuous.measurable]
  have hcomp : (permuteFullOverlap e) ∘
      (physicalFullOverlapCoordinates (N := n+2) (m := m)) =
      (physicalFullOverlapCoordinates (N := n+2) (m := m)) ∘
        permuteReplicas e := by
    funext σ
    exact permuteFullOverlap_physical e σ
  rw [hcomp, ← Measure.map_map physicalFullOverlapCoordinates_continuous.measurable
    (permuteReplicas_measurable e)]
  rw [physicalReplicaLaw_permute]

def exchangeableFullOverlapLawArrays : Set FullOverlapLawArray :=
  {x | ∀ m (e : Equiv.Perm (Fin m)),
    (x m).map (permuteFullOverlap e) = x m}

theorem exchangeableFullOverlapLawArrays_closed :
    IsClosed exchangeableFullOverlapLawArrays := by
  unfold exchangeableFullOverlapLawArrays
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro m
  apply isClosed_iInter
  intro e
  exact isClosed_eq
    ((ProbabilityMeasure.continuous_map (permuteFullOverlap_continuous e)).comp
      (continuous_apply m))
    (continuous_apply m)

theorem physicalFullOverlapArrayLimitSet_exchangeable
    (μ : FiniteMixture) (β : ℝ)
    {x : FullOverlapLawArray} (hx : x ∈ physicalFullOverlapArrayLimitSet μ β) :
    x ∈ exchangeableFullOverlapLawArrays := by
  apply closure_minimal _ exchangeableFullOverlapLawArrays_closed hx
  rintro x ⟨n, rfl⟩ m e
  exact physicalFullOverlapLaw_permute μ β e

end SlowEquilibration.PureCapturePhysicalFullOverlapArray
