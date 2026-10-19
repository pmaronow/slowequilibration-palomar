-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixedReplicaMeanEnergyAssembly
public import SlowEquilibration.MixedHighEnergyRelocation
public import SlowEquilibration.PureCapturePhysicalCoarseDiniAssembly
public import SlowEquilibration.SourceReductionClosedBandGraph

/-! Manuscript `prop:mb-coarse`, assembled from the three physical inputs.
The original Gibbs full-array DS representation, compactness and Dini
machinery supplies companion blocks. Their contact-mean energy is the
center-field energy of the training center. Radial-aware relocation then
puts the query in a two-sided latitude-sqrt-Q band. The replica count is
chosen before one overlap tolerance, uniformly in the physical dimension. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.MixedCapturePhysicalCoarseDiniAssembly

open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalGaussianJet SphericalAging.HardSphereDynamics SphericalBarycenter
open SphericalMarkedWindows
open MixedCaptureReplicaGeometry MixedCapturePhysicalReplicaGeometry
open MixedReplicaMeanEnergyAssembly MixedHighEnergyRelocation
open PureCapturePhysicalCoarseTransfer PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalFiniteMeasurability PureCapturePhysicalLowEnergyMeasurability
open PureCapturePhysicalCoarseLimit PureCapturePhysicalCoarseDiniAssembly
open PureCapturePhysicalAsymptoticFullCompletion PureCapturePhysicalAsymptoticScoreLimits
open PureCapturePhysicalAsymptoticFullLift PureCapturePhysicalFullToScore
open PureCapturePhysicalDSFiniteBridge
open PureCaptureRandomDirectingScoreArray PureCaptureOverlapScoreCoordinates
open PairConditionalDeterminantMoments SourceReductionClosedBandGraph
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Literal physical bands around all high center-field critical points
whose normalized radial mark lies in the prescribed set. -/
def originalCoarseBandUnion (n : ℕ) (μ : FiniteMixture) (Q E τ b : ℝ)
    (U : Set ℝ) (J : Disorder (n+2) μ.maxDegree) : Set (Vector (n+2)) :=
  {σ | ‖σ‖^2 = (n+2 : ℕ) ∧ ∃ u : Vector (n+2),
    ‖u‖^2 = (n+2 : ℕ) ∧
    surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 ∧
    (n+2 : ℕ) * (E-τ) ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J u ∧
    actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U ∧
    |overlap σ u - Real.sqrt Q| ≤ b}

/-- Both the disorder and Gibbs laws are those of the original mixture. -/
def originalCoarseBandComplementMass (n : ℕ) (μ : FiniteMixture)
    (Q E τ b β : ℝ) (U : Set ℝ) (J : Disorder (n+2) μ.maxDegree) : ℝ :=
  (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).real
    (originalCoarseBandUnion n μ Q E τ b U J)ᶜ

/-- The original-disorder expectation of the physical uncovered mass. -/
def expectedOriginalCoarseBandComplementMass (n : ℕ) (μ : FiniteMixture)
    (β Q E τ b : ℝ) (U : Set ℝ) : ℝ :=
  ∫ J, originalCoarseBandComplementMass n μ Q E τ b β U J
    ∂disorderLaw (n+2) μ.maxDegree

private theorem coarseBand_graph_closed (n : ℕ) (μ : FiniteMixture)
    (Q E τ b : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    IsClosed {z : Disorder (n+2) μ.maxDegree × Vector (n+2) |
      z.2 ∈ originalCoarseBandUnion n μ Q E τ b U z.1} := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let S := {u : Vector (n+2) | ‖u‖^2 = (n+2 : ℕ)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (sourceSphere_compact (n+2))
  let C : Set (Disorder (n+2) μ.maxDegree × S) :=
    {z | surfaceGradient (field c z.1) z.2.1 = 0 ∧
      (n+2 : ℕ)*(E-τ) ≤ field c z.1 z.2.1 ∧
      actualScore c z.1 z.2.1 1 ∈ U}
  let B : Set (Vector (n+2) × S) :=
    {z | |overlap z.1 z.2.1 - Real.sqrt Q| ≤ b}
  have hmap : Continuous (fun z : Disorder (n+2) μ.maxDegree × S => (z.1,z.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hC : IsClosed C := by
    exact (isClosed_eq ((source_surfaceGradient_joint_contDiff c).continuous.comp hmap)
      continuous_const).inter
      ((isClosed_le continuous_const ((field_jointContinuous c).comp hmap)).inter
        (hU.preimage (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
          (actualScore_jointContinuous c)).comp hmap)))
  have hB : IsClosed B :=
    (physicalBandRelation_isClosed Q b).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hp := (SourceReductionCompactBandProjection.bandUnionGraph_isClosed hC hB).inter
    (isClosed_eq (continuous_snd.norm.pow 2)
      (continuous_const (y := ((n+2 : ℕ) : ℝ))))
  convert hp using 1
  ext z
  constructor
  · rintro ⟨hσ,u,hu,hg,he,hr,hb⟩
    exact ⟨⟨⟨u,hu⟩,⟨hg,he,hr⟩,hb⟩,hσ⟩
  · rintro ⟨⟨u,⟨hg,he,hr⟩,hb⟩,hσ⟩
    exact ⟨hσ,u.1,u.2,hg,he,hr,hb⟩

/-- Open radial intervals are countable unions of closed interior windows;
compact projection therefore still gives a Borel coarse-band graph. -/
private theorem coarseBand_graph_measurable_open_interval (n : ℕ) (μ : FiniteMixture)
    (Q E τ b L R : ℝ) :
    MeasurableSet {z : Disorder (n+2) μ.maxDegree × Vector (n+2) |
      z.2 ∈ originalCoarseBandUnion n μ Q E τ b (Ioo L R) z.1} := by
  have heq : {z : Disorder (n+2) μ.maxDegree × Vector (n+2) |
      z.2 ∈ originalCoarseBandUnion n μ Q E τ b (Ioo L R) z.1} =
      ⋃ j : ℕ, {z : Disorder (n+2) μ.maxDegree × Vector (n+2) |
        z.2 ∈ originalCoarseBandUnion n μ Q E τ b
          (Icc (L+1/(j+1 : ℝ)) (R-1/(j+1 : ℝ))) z.1} := by
    ext z
    constructor
    · rintro ⟨hσ,u,hu,hg,he,hr,hband⟩
      obtain ⟨j,hj⟩ := exists_nat_one_div_lt
        (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2))
      have hjL := hj.trans_le (min_le_left _ _)
      have hjR := hj.trans_le (min_le_right _ _)
      exact mem_iUnion.mpr ⟨j,hσ,u,hu,hg,he,⟨by linarith,by linarith⟩,hband⟩
    · intro hz
      obtain ⟨j,hσ,u,hu,hg,he,hr,hband⟩ := mem_iUnion.mp hz
      have hjpos : 0 < 1/(j+1 : ℝ) := by positivity
      exact ⟨hσ,u,hu,hg,he,⟨by linarith [hr.1],by linarith [hr.2]⟩,hband⟩
  rw [heq]
  exact MeasurableSet.iUnion fun j =>
    (coarseBand_graph_closed n μ Q E τ b
      (show IsClosed (Icc (L+1/(j+1 : ℝ)) (R-1/(j+1 : ℝ))) from isClosed_Icc)).measurableSet

private theorem coarseBand_probability_measurable_of_graph
    (n : ℕ) (μ : FiniteMixture) (Q E τ b β : ℝ) (U : Set ℝ)
    (hgraph : MeasurableSet {z : Disorder (n+2) μ.maxDegree × Vector (n+2) |
      z.2 ∈ originalCoarseBandUnion n μ Q E τ b U z.1}) :
    Measurable (originalCoarseBandComplementMass n μ Q E τ b β U) := by
  have hm := (Kernel.measurable_kernel_prodMk_left
    (κ := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β)
    hgraph.compl).ennreal_toReal
  convert hm using 1
  funext J
  rw [allDimensionGibbsKernel_apply]
  rfl

private theorem coarseBand_probability_integrable_of_graph
    (n : ℕ) (μ : FiniteMixture) (Q E τ b β : ℝ) (U : Set ℝ)
    (hgraph : MeasurableSet {z : Disorder (n+2) μ.maxDegree × Vector (n+2) |
      z.2 ∈ originalCoarseBandUnion n μ Q E τ b U z.1}) :
    Integrable (originalCoarseBandComplementMass n μ Q E τ b β U)
      (disorderLaw (n+2) μ.maxDegree) := by
  apply Integrable.of_bound
    (coarseBand_probability_measurable_of_graph n μ Q E τ b β U hgraph).aestronglyMeasurable 1
  refine .of_forall fun J => ?_
  let : IsProbabilityMeasure (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  unfold originalCoarseBandComplementMass
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

/-- For closed radial sets, the displayed annealed mass is the integral
of a bounded Borel original-disorder probability. -/
theorem originalCoarseBandComplementMass_integrable_closed
    (n : ℕ) (μ : FiniteMixture) (Q E τ b β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) :
    Integrable (originalCoarseBandComplementMass n μ Q E τ b β U)
      (disorderLaw (n+2) μ.maxDegree) :=
  coarseBand_probability_integrable_of_graph n μ Q E τ b β U
    (coarseBand_graph_closed n μ Q E τ b hU).measurableSet

/-- The open radial interval produced by mixed relocation also gives a
genuine integrable original-disorder coarse-band probability. -/
theorem originalCoarseBandComplementMass_integrable_open_interval
    (n : ℕ) (μ : FiniteMixture) (Q E τ b β L R : ℝ) :
    Integrable (originalCoarseBandComplementMass n μ Q E τ b β (Ioo L R))
      (disorderLaw (n+2) μ.maxDegree) :=
  coarseBand_probability_integrable_of_graph n μ Q E τ b β (Ioo L R)
    (coarseBand_graph_measurable_open_interval n μ Q E τ b L R)

set_option linter.unusedVariables false in
/-- The scalar continuity argument is independent of the vector dimension;
the finite-replica diagonal correction is retained before choosing tolerance. -/
private theorem exists_replica_count_and_band_tolerance
    {Q b : ℝ} (hQ : Q ∈ Icc (0 : ℝ) 1) (hb : 0 < b) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ 0 < k ∧ ∃ θ : ℝ, 0 < θ ∧ θ < correctedNormSq Q k / 2 ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (x : Vector N) (σ : Fin k → Vector N),
        OnSphere x → (∀ i, OnSphere (σ i)) → goodCompanionBlock Q θ x σ →
        ‖physicalTrainingCenter σ‖ ^ 2 = (N : ℝ) ∧
          0 < physicalMeanNormSq σ ∧
          |overlap x (physicalTrainingCenter σ) - Real.sqrt Q| < b / 2 := by
  have hlarge : ∀ᶠ k : ℕ in atTop,
      |Q / Real.sqrt (correctedNormSq Q k) - Real.sqrt Q| < b / 4 := by
    by_cases hpos : 0 < Q
    · have hh := (corrected_query_tendsto hpos).eventually
        (Metric.ball_mem_nhds _ (by linarith : 0 < b / 4))
      simpa only [Metric.mem_ball, Real.dist_eq] using hh
    · have hzero : Q = 0 := le_antisymm (not_lt.mp hpos) hQ.1
      exact .of_forall fun k => by simpa only [hzero, zero_div, Real.sqrt_zero,
        sub_zero, abs_zero] using (show (0 : ℝ) < b/4 by positivity)
  obtain ⟨k, hk₀, hk, hdiag⟩ := ((eventually_ge_atTop k₀).and
    ((eventually_gt_atTop 0).and hlarge)).exists
  let qk := correctedNormSq Q k
  have hqk : 0 < qk := by
    by_cases hpos : 0 < Q
    · exact hpos.trans_le (correctedNormSq_ge hQ.2 hk)
    · have hzero : Q = 0 := le_antisymm (not_lt.mp hpos) hQ.1
      simp only [qk, correctedNormSq, hzero, zero_add, sub_zero]
      exact div_pos (by norm_num) (Nat.cast_pos.mpr hk)
  have hcont : ContinuousAt (fun p : ℝ × ℝ => p.2 / Real.sqrt p.1) (qk, Q) :=
    continuous_snd.continuousAt.div
      (Real.continuous_sqrt.continuousAt.comp continuous_fst.continuousAt)
      (Real.sqrt_ne_zero'.mpr hqk)
  obtain ⟨ε, hε, hcontrol⟩ :=
    Metric.continuousAt_iff.mp hcont (b / 4) (by linarith)
  let θ := min (ε / 2) (qk / 4)
  have hθ : 0 < θ := lt_min (half_pos hε) (by positivity)
  have hθqk : θ < qk / 2 :=
    (min_le_right _ _).trans_lt (by linarith)
  have hθε : θ < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨k, hk₀, hk, θ, hθ, hθqk, ?_⟩
  intro N hN x σ hx hσ hgood
  have hunit (i : Fin k) : ‖spin (σ i)‖ ^ 2 = 1 := by
    rw [spin_norm hN _ (hσ i), one_pow]
  have hpair : ∀ i j : Fin k, i ≠ j →
      |inner ℝ (spin (σ i)) (spin (σ j)) - Q| ≤ θ := by
    intro i j hij
    simpa only [spin_inner hN] using (hgood.1 i j hij).le
  have hquery : ∀ i : Fin k,
      |inner ℝ (spin x) (spin (σ i)) - Q| ≤ θ := by
    intro i
    simpa only [spin_inner hN] using (hgood.2 i).le
  have hnorm := replicaMean_norm_sq_error hk
    (fun i => spin (σ i)) hunit hθ.le hpair
  have hmean := query_replicaMean_error hk
    (fun i => spin (σ i)) (spin x) hquery
  have hdist : dist (‖replicaMean (fun i => spin (σ i))‖ ^ 2,
      inner ℝ (spin x) (replicaMean (fun i => spin (σ i)))) (qk, Q) ≤ θ := by
    rw [Prod.dist_eq]
    exact max_le (by simpa only [Real.dist_eq] using hnorm)
      (by simpa only [Real.dist_eq] using hmean)
  have hout := hcontrol (hdist.trans_lt hθε)
  have hmeanpos : 0 < ‖replicaMean (fun i => spin (σ i))‖^2 := by
    have hh := (abs_le.mp hnorm).1
    change -θ ≤ ‖replicaMean (fun i => spin (σ i))‖^2-qk at hh
    linarith
  have hmean_ne : replicaMean (fun i => spin (σ i)) ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), lt_self_iff_false] at hmeanpos
  have hsphere : ‖physicalTrainingCenter σ‖^2 = (N : ℝ) := by
    rw [physicalTrainingCenter, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      normalizedReplicaMean_norm _ hmean_ne, mul_one, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hpos : 0 < physicalMeanNormSq σ := by
    rw [physicalMeanNormSq_eq_unitMeanNormSq hN]
    exact hmeanpos
  refine ⟨hsphere, hpos, ?_⟩
  have heq : overlap x (physicalTrainingCenter σ) =
      inner ℝ (spin x) (replicaMean (fun i => spin (σ i))) /
        Real.sqrt (‖replicaMean (fun i => spin (σ i))‖ ^ 2) := by
    rw [← spin_inner hN, spin_physicalTrainingCenter hN,
      normalizedReplicaMean, real_inner_smul_right,
      Real.sqrt_sq (norm_nonneg _)]
    ring
  have habs : |inner ℝ (spin x) (replicaMean (fun i => spin (σ i))) /
      Real.sqrt (‖replicaMean (fun i => spin (σ i))‖ ^ 2) -
        Q / Real.sqrt qk| < b / 4 := by
    simpa only [Real.dist_eq] using hout
  rw [heq]
  have htriangle := abs_sub_le
    (inner ℝ (spin x) (replicaMean (fun i => spin (σ i))) /
      Real.sqrt (‖replicaMean (fun i => spin (σ i))‖ ^ 2))
    (Q / Real.sqrt qk) (Real.sqrt Q)
  change |Q / Real.sqrt qk - Real.sqrt Q| < b / 4 at hdiag
  linarith

private theorem contactLowEnergy_probability_integrable {n k : ℕ}
    (μ : FiniteMixture) (β Q η E ε : ℝ) :
    Integrable (fun J : Disorder (n+2) μ.maxDegree =>
      (Measure.pi (fun _ : Fin k => gibbsLaw (n+2) β
        (field (mixtureCoefficients μ) J))).real
        (contactReplicaMeanLowEnergy μ J Q η E ε))
      (disorderLaw (n+2) μ.maxDegree) := by
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  have h := (Kernel.measurable_kernel_prodMk_left
    (κ := GaussianReplicaKernel.iid G k)
      (joint_contactReplicaMeanLowEnergy_measurable (k := k) μ Q η E ε)).ennreal_toReal
  have hm : Measurable (fun J : Disorder (n+2) μ.maxDegree =>
      (Measure.pi (fun _ : Fin k => gibbsLaw (n+2) β
        (field (mixtureCoefficients μ) J))).real
        (contactReplicaMeanLowEnergy μ J Q η E ε)) := by
    convert h using 1
    funext J
    simp only [GaussianReplicaKernel.iid_apply, G, allDimensionGibbsKernel_apply]
    rfl
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  refine .of_forall fun J => ?_
  let : IsProbabilityMeasure (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

/-- One query and finitely many ordinary companion blocks give a union
bound by score failure and the original-model contact low-energy event. -/
private theorem physical_band_complement_le_failure_add_contactEnergy
    {n k T : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder (n+2) μ.maxDegree) {Q θ η E τ τ₁ b : ℝ}
    (hQ : 0 ≤ Q) (hθη : θ ≤ η) (hτ : τ₁ ≤ τ) (hb : 0 < b)
    (U : Set ℝ)
    (hscore : ∀ x : Vector (n+2), ∀ σ : Fin k → Vector (n+2),
      OnSphere x → (∀ i, OnSphere (σ i)) → goodCompanionBlock Q θ x σ →
      ‖physicalTrainingCenter σ‖^2 = (n+2 : ℕ) ∧
        0 < physicalMeanNormSq σ ∧
        |overlap x (physicalTrainingCenter σ) - Real.sqrt Q| < b/2)
    (hrelocate : ∀ w : Vector (n+2), ‖w‖^2 = (n+2 : ℕ) →
      (n+2 : ℕ)*(E-τ₁) ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J w →
      ∃ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) ∧
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 ∧
        actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U ∧
        ‖u-w‖ ≤ (b/4)*Real.sqrt (n+2 : ℕ) ∧
        field (centerCoefficients (mixtureCoefficients μ) Q) J w ≤
          field (centerCoefficients (mixtureCoefficients μ) Q) J u) :
    originalCoarseBandComplementMass n μ Q E τ b β U J ≤
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real (allBlocksFail Q θ) +
      (T : ℝ)*(Measure.pi (fun _ : Fin k => gibbsLaw (n+2) β
        (field (mixtureCoefficients μ) J))).real
        (contactReplicaMeanLowEnergy μ J Q η E τ₁) := by
  let π := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)
  let ρ := Measure.pi (fun _ : Fin k => π)
  let ν := physicalEnsembleLaw (k := k) (T := T) μ β J
  let C := originalCoarseBandUnion n μ Q E τ b U J
  let S : Set (PhysicalEnsemble (n+2) k T) := allPhysicalSpinsOnSphere
  let A : Set (PhysicalEnsemble (n+2) k T) := {p | p.1 ∉ C}
  let F : Set (PhysicalEnsemble (n+2) k T) := allBlocksFail Q θ
  let L := contactReplicaMeanLowEnergy (k := k) μ J Q η E τ₁
  let D : Set (PhysicalEnsemble (n+2) k T) := ⋃ j : Fin T, {p | p.2 j ∈ L}
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
  have hL : MeasurableSet L := contactReplicaMeanLowEnergy_measurable μ J Q η E τ₁
  have hAset : A = Cᶜ ×ˢ univ := by ext p; simp [A, Set.mem_prod]
  have hA : ν.real A = π.real Cᶜ := by
    rw [hAset]
    change (π.prod (Measure.pi (fun _ : Fin T => ρ))).real (Cᶜ ×ˢ univ) = _
    rw [measureReal_prod_prod, probReal_univ, mul_one]
  have hSzero : ν.real Sᶜ = 0 := by
    have hnull : ν Sᶜ = 0 := by
      simpa only [ν, S, Set.ofPred_mem_eq] using
        (mem_ae_iff.mp (physicalEnsembleLaw_sphere_ae (k := k) (T := T) μ β J))
    rw [Measure.real, hnull, ENNReal.toReal_zero]
  have hsub : A ⊆ Sᶜ ∪ (F ∪ D) := by
    intro p hp
    by_cases hs : p ∈ S
    · right
      by_cases hf : p ∈ F
      · exact Or.inl hf
      · right
        have hsome : ∃ j : Fin T, goodCompanionBlock Q θ p.1 (p.2 j) := by
          simpa only [F, allBlocksFail, Set.mem_ofPred_eq, not_forall, not_not] using hf
        obtain ⟨j, hj⟩ := hsome
        refine mem_iUnion.mpr ⟨j, ?_⟩
        by_contra hlow
        have hpair : ∀ i l : Fin k, i ≠ l → |overlap (p.2 j i) (p.2 j l)-Q| < η :=
          fun i l hil => (hj.1 i l hil).trans_le hθη
        have hhigh : (n+2 : ℕ)*(E-τ₁) ≤
            field (mixtureCoefficients μ) J (physicalContactMean Q (p.2 j)) := by
          have hh : ¬ field (mixtureCoefficients μ) J (physicalContactMean Q (p.2 j)) ≤
              (n+2 : ℕ)*(E-τ₁) := fun h => hlow ⟨hpair, h⟩
          exact (not_le.mp hh).le
        obtain ⟨hw, hpos, hquery⟩ := hscore p.1 (p.2 j) hs.1 (fun i => hs.2 j i) hj
        rw [← field_trainingCenter_eq_contactMean μ hQ J (p.2 j) hpos] at hhigh
        obtain ⟨u, hu, hcrit, hradial, hdist, hvalue⟩ := hrelocate _ hw hhigh
        have henergy : (n+2 : ℕ)*(E-τ) ≤
            field (centerCoefficients (mixtureCoefficients μ) Q) J u := by
          exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hτ E)
            (Nat.cast_nonneg _)).trans (hhigh.trans hvalue)
        have hmove₁ := physical_overlap_sub_le_of_center_distance (by omega : 1 ≤ n+2)
          p.1 (physicalTrainingCenter (p.2 j)) u hs.1 hdist
        have hdist' : ‖physicalTrainingCenter (p.2 j)-u‖ ≤ (b/4)*Real.sqrt (n+2 : ℕ) := by
          simpa only [norm_sub_rev] using hdist
        have hmove₂ := physical_overlap_sub_le_of_center_distance (by omega : 1 ≤ n+2)
          p.1 u (physicalTrainingCenter (p.2 j)) hs.1 hdist'
        have hmove : |overlap p.1 u - overlap p.1 (physicalTrainingCenter (p.2 j))| ≤ b/4 :=
          abs_le.mpr ⟨by linarith, hmove₂⟩
        have hband : |overlap p.1 u - Real.sqrt Q| ≤ b := by
          have ht := abs_sub_le (overlap p.1 u)
            (overlap p.1 (physicalTrainingCenter (p.2 j))) (Real.sqrt Q)
          linarith
        exact hp ⟨(onSphere_iff_norm_sq p.1).mp hs.1, u, hu, hcrit, henergy, hradial, hband⟩
    · exact Or.inl hs
  have hmarg (j : Fin T) : ν.real {p : PhysicalEnsemble (n+2) k T | p.2 j ∈ L} = ρ.real L := by
    have hMP : MeasurePreserving (fun p : PhysicalEnsemble (n+2) k T => p.2 j) ν ρ :=
      (measurePreserving_eval (μ := fun _ : Fin T => ρ) j).comp measurePreserving_snd
    exact hMP.measureReal_preimage hL.nullMeasurableSet
  have hD : ν.real D ≤ (T : ℝ)*ρ.real L := by
    calc
      _ ≤ ∑ j : Fin T, ν.real {p : PhysicalEnsemble (n+2) k T | p.2 j ∈ L} :=
        measureReal_iUnion_fintype_le _
      _ = _ := by
        simp only [hmarg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    originalCoarseBandComplementMass n μ Q E τ b β U J = ν.real A := hA.symm
    _ ≤ ν.real (Sᶜ ∪ (F ∪ D)) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ν.real Sᶜ + ν.real (F ∪ D) := measureReal_union_le _ _
    _ ≤ ν.real F + ν.real D := by rw [hSzero, zero_add]; exact measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl hD

private theorem physical_normQ_range (μ : FiniteMixture) (β Q : ℝ)
    (hNorm : PhysicalDirectingNormQ μ β Q) : Q ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨z, hz, _, _, _⟩ :=
    physicalFullAsymptoticLimitSet_tendsto_subseq μ β id strictMono_id
  obtain ⟨R, hrep, hball⟩ := physicalFullAsymptoticLimit_randomDirecting μ β hz
  let : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hQ := hNorm z hz R hrep hball
  obtain ⟨ω, hωball, hωQ⟩ := (hball.and hQ).exists
  obtain ⟨v, hvball, hvQ⟩ := (hωball.and hωQ).exists
  rw [← hvQ]
  exact ⟨sq_nonneg _, by nlinarith [norm_nonneg v]⟩

/-- Source `prop:mb-coarse`: the three physical inputs imply capture by
arbitrarily narrow two-sided bands with the prescribed radial marks. -/
theorem physical_coarse_cover_of_three_physical_inputs
    (μ : FiniteMixture) (β : ℝ) {Q E : ℝ} (U : Set ℝ)
    (hNorm : PhysicalDirectingNormQ μ β Q)
    (hMean : PhysicalContactReplicaMeanEnergy μ β Q E)
    (hRelocate : CenterFieldRelocation μ Q E U) :
    ∀ b : ℝ, 0 < b → ∀ τ : ℝ, 0 < τ → Tendsto
      (fun n => expectedOriginalCoarseBandComplementMass n μ β Q E τ b U)
      atTop (𝓝 (0 : ℝ)) := by
  have hQ : Q ∈ Icc (0 : ℝ) 1 := physical_normQ_range μ β Q hNorm
  intro b hb τ hτ
  obtain ⟨τ₀, hτ₀, Ω, hΩ, hrelocate, hrelocateProb⟩ :=
    hRelocate (b/4) (by positivity)
  let τ₁ := min τ τ₀
  have hτ₁ : 0 < τ₁ := lt_min hτ hτ₀
  obtain ⟨k₀, η, hη, hmean⟩ := hMean τ₁ hτ₁
  obtain ⟨k, hk₀, _, θ₀, hθ₀, _, hgeometry⟩ :=
    exists_replica_count_and_band_tolerance hQ hb k₀
  let θ := min θ₀ η
  have hθ : 0 < θ := lt_min hθ₀ hη
  have hscore : ∀ n : ℕ, ∀ x : Vector (n+2), ∀ σ : Fin k → Vector (n+2),
      OnSphere x → (∀ i, OnSphere (σ i)) → goodCompanionBlock Q θ x σ →
      ‖physicalTrainingCenter σ‖^2 = (n+2 : ℕ) ∧ 0 < physicalMeanNormSq σ ∧
        |overlap x (physicalTrainingCenter σ) - Real.sqrt Q| < b/2 := by
    intro n x σ hx hσ hgood
    exact hgeometry (n+2) (by omega) x σ hx hσ
      ⟨fun i j hij => (hgood.1 i j hij).trans_le (min_le_left θ₀ η),
        fun i => (hgood.2 i).trans_le (min_le_left θ₀ η)⟩
  have hrelocate' : ∀ n, ∀ J ∈ Ω n, ∀ w : Vector (n+2),
      ‖w‖^2 = (n+2 : ℕ) →
      (n+2 : ℕ)*(E-τ₁) ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J w →
      ∃ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) ∧
        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 ∧
        actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U ∧
        ‖u-w‖ ≤ (b/4)*Real.sqrt (n+2 : ℕ) ∧
        field (centerCoefficients (mixtureCoefficients μ) Q) J w ≤
          field (centerCoefficients (mixtureCoefficients μ) Q) J u := by
    intro n J hJ w hw he
    apply hrelocate n J hJ w hw
    exact (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (min_le_right τ τ₀) E) (Nat.cast_nonneg _)).trans he
  have hpoint := pointwise_scoreFailure_of_asymptotic_full_directing_representation
    μ β Q θ hθ (normQ_score_representation_of_physical_norm μ β Q hNorm k)
  have hbound (n T : ℕ) : expectedOriginalCoarseBandComplementMass n μ β Q E τ b U ≤
      (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ +
      expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ +
      (T : ℝ)*expectedContactReplicaMeanLowEnergy (k := k) n μ β Q η E τ₁ := by
    let d := disorderLaw (n+2) μ.maxDegree
    let I : Disorder (n+2) μ.maxDegree → ℝ := (Ω n)ᶜ.indicator (fun _ => 1)
    let F := fun J : Disorder (n+2) μ.maxDegree =>
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real (allBlocksFail Q θ)
    let L := fun J : Disorder (n+2) μ.maxDegree =>
      (Measure.pi (fun _ : Fin k => gibbsLaw (n+2) β
        (field (mixtureCoefficients μ) J))).real (contactReplicaMeanLowEnergy μ J Q η E τ₁)
    have hI : Integrable I d := (integrable_const 1).indicator (hΩ n).compl
    have hF : Integrable F d := finiteFailureProbability_integrable μ β Q θ
    have hL : Integrable L d := contactLowEnergy_probability_integrable μ β Q η E τ₁
    have hle (J : Disorder (n+2) μ.maxDegree) :
        originalCoarseBandComplementMass n μ Q E τ b β U J ≤ I J + F J + (T : ℝ)*L J := by
      by_cases hJ : J ∈ Ω n
      · have hh := physical_band_complement_le_failure_add_contactEnergy (T := T)
          μ β J hQ.1 (min_le_right θ₀ η) (min_le_left τ τ₀) hb U
          (hscore n) (hrelocate' n J hJ)
        have hz : I J = 0 := Set.indicator_of_notMem (by simpa using hJ) _
        simpa only [hz, zero_add] using hh
      · have hmass : originalCoarseBandComplementMass n μ Q E τ b β U J ≤ 1 := by
          let : IsProbabilityMeasure (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) :=
            gibbsLaw_probability (by omega) β (field_contDiff (mixtureCoefficients μ) J).continuous
          exact measureReal_le_one
        have hF0 : 0 ≤ F J := measureReal_nonneg
        have hL0 : 0 ≤ (T : ℝ)*L J := mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
        have hJc : J ∈ (Ω n)ᶜ := hJ
        simp only [I, Set.indicator_of_mem hJc]
        linarith
    have hi := integral_mono_of_nonneg (.of_forall fun _ => measureReal_nonneg)
      ((hI.add hF).add (hL.const_mul (T : ℝ))) (.of_forall hle)
    have hIeq : (∫ J, I J ∂d) = d.real (Ω n)ᶜ := by
      rw [integral_indicator_const 1 (hΩ n).compl, smul_eq_mul, mul_one]
    change expectedOriginalCoarseBandComplementMass n μ β Q E τ b U ≤
      ∫ J, (I + F) J + (T : ℝ)*L J ∂d at hi
    rw [integral_add (hI.add hF) (hL.const_mul (T : ℝ))] at hi
    change expectedOriginalCoarseBandComplementMass n μ β Q E τ b U ≤
      (∫ J, I J + F J ∂d) + ∫ J, (T : ℝ)*L J ∂d at hi
    rw [integral_add hI hF, hIeq, integral_const_mul] at hi
    exact hi
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact .of_forall fun n => hc.trans_le (integral_nonneg fun _ => measureReal_nonneg)
  · intro ε hε
    have hthird : 0 < ε/3 := by positivity
    obtain ⟨T, hfailure⟩ := expectedFiniteFailure_eventually_small_of_asymptotic_limits
      μ β Q θ hpoint (ε/3) hthird
    have henergy : Tendsto (fun n =>
        (T : ℝ)*expectedContactReplicaMeanLowEnergy (k := k) n μ β Q η E τ₁)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using (hmean k hk₀).const_mul (T : ℝ)
    filter_upwards [hfailure, hrelocateProb.eventually (gt_mem_nhds hthird),
      henergy.eventually (gt_mem_nhds hthird)] with n hF hR hE
    linarith [hbound n T]

end SlowEquilibration.MixedCapturePhysicalCoarseDiniAssembly
