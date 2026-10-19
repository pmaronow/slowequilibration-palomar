-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalCoarseTransfer
public import SlowEquilibration.GaussianReplicaKernel

/-! The finite-ensemble implication in manuscript Proposition 9.16. A query
Gibbs spin and finitely many fixed-size companion blocks are sampled under
the literal physical Gibbs law. Failure to be in the critical cap entails
either that every companion block fails the overlap score or that a
successful block has low empirical-mean energy, on the source relocation
event. The asymptotic bounds for those two alternatives are separate. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFiniteEnsembleTransfer

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging.HardSphereDynamics
open PureCapturePhysicalDiagonalBridge PureCapturePhysicalCoarseTransfer
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual finite array has one distinguished query spin and T
independent companion blocks, each containing k ordinary Gibbs spins. -/
abbrev PhysicalEnsemble (N k T : ℕ) :=
  Vector N × (Fin T → Fin k → Vector N)

/-- Strict finite overlap score: every distinct companion pair and each
query-companion pair lies within theta of Q. -/
def goodCompanionBlock {N k : ℕ} (Q θ : ℝ)
    (x : Vector N) (σ : Fin k → Vector N) : Prop :=
  (∀ i j : Fin k, i ≠ j → |overlap (σ i) (σ j) - Q| < θ) ∧
  (∀ i : Fin k, |overlap x (σ i) - Q| < θ)

def allBlocksFail {N k T : ℕ} (Q θ : ℝ) : Set (PhysicalEnsemble N k T) :=
  {p | ∀ b : Fin T, ¬goodCompanionBlock Q θ p.1 (p.2 b)}

def someSuccessfulBlockLowEnergy {N k T : ℕ} (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (Q θ e τ₁ : ℝ) :
    Set (PhysicalEnsemble N k T) :=
  {p | ∃ b : Fin T, goodCompanionBlock Q θ p.1 (p.2 b) ∧
    field (mixtureCoefficients μ) J (physicalTrainingCenter (p.2 b)) <
      (N : ℝ) * (e-τ₁)}

def allPhysicalSpinsOnSphere {N k T : ℕ} : Set (PhysicalEnsemble N k T) :=
  {p | OnSphere p.1 ∧ ∀ b i, OnSphere (p.2 b i)}

/-- Ordinary finite product of the original, disorder-conditioned Gibbs
law: one query, then T independent k-replica companion blocks. -/
def physicalEnsembleLaw {n k T : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder (n+2) μ.maxDegree) : Measure (PhysicalEnsemble (n+2) k T) :=
  let π := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)
  π.prod (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => π)))

instance physicalEnsembleLaw_probability {n k T : ℕ} (μ : FiniteMixture)
    (β : ℝ) (J : Disorder (n+2) μ.maxDegree) :
    IsProbabilityMeasure (physicalEnsembleLaw (k := k) (T := T) μ β J) := by
  unfold physicalEnsembleLaw
  let : IsProbabilityMeasure (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  infer_instance

theorem allPhysicalSpinsOnSphere_measurable {N k T : ℕ} :
    MeasurableSet (allPhysicalSpinsOnSphere (N := N) (k := k) (T := T)) := by
  have hS : MeasurableSet {x : Vector N | OnSphere x} := by
    have hclosed : IsClosed {x : Vector N | ‖x‖ ^ 2 = (N : ℝ)} :=
      isClosed_eq (continuous_norm.pow 2) continuous_const
    convert hclosed.measurableSet using 1
    ext x
    exact onSphere_iff_norm_sq x
  have hquery : MeasurableSet {p : PhysicalEnsemble N k T | OnSphere p.1} :=
    hS.preimage measurable_fst
  have hblocks : MeasurableSet
      {p : PhysicalEnsemble N k T | ∀ b : Fin T, ∀ i : Fin k, OnSphere (p.2 b i)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro i
    exact hS.preimage ((measurable_pi_apply i).comp
      ((measurable_pi_apply b).comp measurable_snd))
  exact hquery.inter hblocks

/-- The original product Gibbs law is supported on physical sphere
replicas in every coordinate, including the distinguished query. -/
theorem physicalEnsembleLaw_sphere_ae {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) (J : Disorder (n+2) μ.maxDegree) :
    ∀ᵐ p ∂physicalEnsembleLaw (k := k) (T := T) μ β J,
      p ∈ allPhysicalSpinsOnSphere := by
  let π := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  have hπ : ∀ᵐ x ∂π, OnSphere x :=
    (gibbsLaw_support (by omega) β (field (mixtureCoefficients μ) J)).mono
      (fun x hx => (onSphere_iff_norm_sq x).mpr hx)
  have hblock : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => π), ∀ i : Fin k, OnSphere (σ i) :=
    Filter.eventually_all.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => π) (i := i)).eventually hπ)
  have hblocks : ∀ᵐ σ ∂Measure.pi (fun _ : Fin T =>
      Measure.pi (fun _ : Fin k => π)),
      ∀ b : Fin T, ∀ i : Fin k, OnSphere (σ b i) :=
    Filter.eventually_all.mpr (fun b =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin T => Measure.pi (fun _ : Fin k => π)) (i := b)).eventually hblock)
  change ∀ᵐ p ∂π.prod (Measure.pi (fun _ : Fin T =>
    Measure.pi (fun _ : Fin k => π))), p ∈ allPhysicalSpinsOnSphere
  apply (Measure.ae_prod_iff_ae_ae allPhysicalSpinsOnSphere_measurable).mpr
  filter_upwards [hπ] with x hx
  filter_upwards [hblocks] with σ hσ
  exact ⟨hx,hσ⟩

/-- Deterministic core of the actual finite-ensemble transfer. The
successful-block score controls the literal normalized empirical mean;
the source relocation event then converts it to a high critical cap. -/
theorem uncovered_good_ensemble_subset_failure_or_lowEnergy
    {n k T : ℕ} (μ : FiniteMixture)
    (J : Disorder (n+2) μ.maxDegree)
    {Q θ a a₁ r e τ τ₁ : ℝ} (hτ : τ₁ ≤ τ) (ha : a < a₁-r)
    (hscore : ∀ x : Vector (n+2), ∀ σ : Fin k → Vector (n+2),
      OnSphere x → (∀ i, OnSphere (σ i)) →
      goodCompanionBlock Q θ x σ →
      ‖physicalTrainingCenter σ‖ ^ 2 = (n+2 : ℕ) ∧
        a₁ < overlap x (physicalTrainingCenter σ))
    (hrelocate : ∀ w : Vector (n+2), ‖w‖ ^ 2 = (n+2 : ℕ) →
      (n+2 : ℕ) * (e-τ₁) ≤ field (mixtureCoefficients μ) J w →
      ∃ u : Vector (n+2),
        ‖u‖ ^ 2 = (n+2 : ℕ) ∧
        surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
        ‖u-w‖ ≤ r*Real.sqrt (n+2 : ℕ) ∧
        field (mixtureCoefficients μ) J w ≤
          field (mixtureCoefficients μ) J u) :
    {p : PhysicalEnsemble (n+2) k T |
      p ∈ allPhysicalSpinsOnSphere ∧
        p.1 ∉ coarseCriticalCapCover n μ a e τ J} ⊆
      allBlocksFail Q θ ∪ someSuccessfulBlockLowEnergy μ J Q θ e τ₁ := by
  intro p hp
  by_cases hfail : p ∈ allBlocksFail Q θ
  · exact Or.inl hfail
  · right
    have hsome : ∃ b : Fin T, goodCompanionBlock Q θ p.1 (p.2 b) := by
      simpa only [allBlocksFail, Set.mem_ofPred_eq, not_forall, not_not] using hfail
    obtain ⟨b,hb⟩ := hsome
    refine ⟨b,hb,?_⟩
    by_contra hlow
    have hhigh : (n+2 : ℕ)*(e-τ₁) ≤
        field (mixtureCoefficients μ) J (physicalTrainingCenter (p.2 b)) :=
      not_lt.mp hlow
    have hcap := hscore p.1 (p.2 b) hp.1.1 (fun i => hp.1.2 b i) hb
    have hrel := hrelocate _ hcap.1 hhigh
    have henergy : (n+2 : ℕ)*(e-τ) ≤
        field (mixtureCoefficients μ) J (physicalTrainingCenter (p.2 b)) := by
      have hN : (0 : ℝ) ≤ (n+2 : ℕ) := Nat.cast_nonneg _
      nlinarith
    exact hp.2 (physical_training_group_mem_criticalCap μ J ha p.1 hp.1.1
      (p.2 b) hcap henergy hrel)

/-- The score control is supplied by the proved physical finite-replica
geometry; the sole remaining finite-dimensional premise is the genuine
high-energy relocation event. -/
theorem exists_tolerance_uncovered_good_ensemble_subset
    {n k T : ℕ} (hk : 0 < k) (μ : FiniteMixture)
    (J : Disorder (n+2) μ.maxDegree)
    {Q a a₁ r e τ τ₁ : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (ha₁ : a₁ < Q / Real.sqrt (MixedCaptureReplicaGeometry.correctedNormSq Q k))
    (hτ : τ₁ ≤ τ) (ha : a < a₁-r)
    (hrelocate : ∀ w : Vector (n+2), ‖w‖ ^ 2 = (n+2 : ℕ) →
      (n+2 : ℕ) * (e-τ₁) ≤ field (mixtureCoefficients μ) J w →
      ∃ u : Vector (n+2),
        ‖u‖ ^ 2 = (n+2 : ℕ) ∧
        surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
        ‖u-w‖ ≤ r*Real.sqrt (n+2 : ℕ) ∧
        field (mixtureCoefficients μ) J w ≤
          field (mixtureCoefficients μ) J u) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Q ∧
      {p : PhysicalEnsemble (n+2) k T |
        p ∈ allPhysicalSpinsOnSphere ∧
          p.1 ∉ coarseCriticalCapCover n μ a e τ J} ⊆
        allBlocksFail Q θ ∪ someSuccessfulBlockLowEnergy μ J Q θ e τ₁ := by
  obtain ⟨θ,hθ,hθQ,hscore⟩ :=
    exists_physicalTrainingCenter_query_tolerance (by omega : 1 ≤ n+2) hk hQ ha₁
  refine ⟨θ,hθ,hθQ,?_⟩
  exact uncovered_good_ensemble_subset_failure_or_lowEnergy μ J hτ ha
    (fun x σ hx hσ hs => hscore x σ hx hσ hs.1 hs.2) hrelocate

/-- Literal one-disorder Gibbs inequality at fixed finite replica counts.
The score and low-energy probabilities here are probabilities under the
ordinary query-plus-block product Gibbs measure, not surrogate measures. -/
theorem physical_uncoveredGibbsMass_le_failure_add_lowEnergy
    {n k T : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder (n+2) μ.maxDegree)
    {Q θ a a₁ r e τ τ₁ : ℝ} (hτ : τ₁ ≤ τ) (ha : a < a₁-r)
    (hscore : ∀ x : Vector (n+2), ∀ σ : Fin k → Vector (n+2),
      OnSphere x → (∀ i, OnSphere (σ i)) →
      goodCompanionBlock Q θ x σ →
      ‖physicalTrainingCenter σ‖ ^ 2 = (n+2 : ℕ) ∧
        a₁ < overlap x (physicalTrainingCenter σ))
    (hrelocate : ∀ w : Vector (n+2), ‖w‖ ^ 2 = (n+2 : ℕ) →
      (n+2 : ℕ) * (e-τ₁) ≤ field (mixtureCoefficients μ) J w →
      ∃ u : Vector (n+2),
        ‖u‖ ^ 2 = (n+2 : ℕ) ∧
        surfaceGradient (field (mixtureCoefficients μ) J) u = 0 ∧
        ‖u-w‖ ≤ r*Real.sqrt (n+2 : ℕ) ∧
        field (mixtureCoefficients μ) J w ≤
          field (mixtureCoefficients μ) J u) :
    uncoveredGibbsMass n μ β a e τ J ≤
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real (allBlocksFail Q θ) +
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real
        (someSuccessfulBlockLowEnergy μ J Q θ e τ₁) := by
  let π := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)
  let ρ := Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => π))
  let ν := physicalEnsembleLaw (k := k) (T := T) μ β J
  let C := coarseCriticalCapCover n μ a e τ J
  let S : Set (PhysicalEnsemble (n+2) k T) := allPhysicalSpinsOnSphere
  let A : Set (PhysicalEnsemble (n+2) k T) := {p | p.1 ∉ C}
  let F : Set (PhysicalEnsemble (n+2) k T) := allBlocksFail Q θ
  let E : Set (PhysicalEnsemble (n+2) k T) :=
    someSuccessfulBlockLowEnergy μ J Q θ e τ₁
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  let : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have hAset : A = Cᶜ ×ˢ univ := by
    ext p
    simp [A,C,Set.mem_prod]
  have hA : ν.real A = π.real Cᶜ := by
    rw [hAset]
    change (π.prod ρ).real (Cᶜ ×ˢ univ) = _
    rw [measureReal_prod_prod, probReal_univ, mul_one]
  have hSzero : ν.real Sᶜ = 0 := by
    have hnull : ν Sᶜ = 0 := by
      simpa only [ν,S,Set.ofPred_mem_eq] using
        (mem_ae_iff.mp (physicalEnsembleLaw_sphere_ae (k := k) (T := T) μ β J))
    rw [Measure.real, hnull, ENNReal.toReal_zero]
  have hsub : A ⊆ Sᶜ ∪ (F ∪ E) := by
    intro p hp
    by_cases hs : p ∈ S
    · right
      exact uncovered_good_ensemble_subset_failure_or_lowEnergy μ J hτ ha hscore
        hrelocate ⟨hs,hp⟩
    · exact Or.inl hs
  have hmono : ν.real A ≤ ν.real (Sᶜ ∪ (F ∪ E)) :=
    measureReal_mono (h₂ := measure_ne_top _ _) hsub
  calc
    uncoveredGibbsMass n μ β a e τ J = ν.real A := hA.symm
    _ ≤ ν.real (Sᶜ ∪ (F ∪ E)) := hmono
    _ ≤ ν.real Sᶜ + ν.real (F ∪ E) := measureReal_union_le _ _
    _ ≤ ν.real F + ν.real E := by
      rw [hSzero, zero_add]
      exact measureReal_union_le _ _

end SlowEquilibration.PureCapturePhysicalFiniteEnsembleTransfer
