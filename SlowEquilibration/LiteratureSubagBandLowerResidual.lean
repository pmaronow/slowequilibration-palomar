-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerProof

/-!
The untruncated residual pressure is separated from the exponential floor.
A lower tail tending to zero and a uniform second moment of the normalized
logarithm suffice for its expectation to tend to zero. This is the precise
uniform integrability step needed after the uniform-frame argument.

This is a further reduction. The physical block-logarithm moment estimate
and the lower tails at the dimension-corrected temperature remain explicit
hypotheses; the full residual limit from Chen alone is not asserted.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagBandLowerResidual

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagTAP
open LiteratureSubagTheorem10Proof LiteratureSubagTheorem10Final
open LiteratureSubagBandLowerProof LiteratureSubagBandUpperFinal
open scoped Topology BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite second-moment bound converts a lower-tail bound into an
untruncated expectation estimate. -/
theorem integral_nonpos_lower_bound_of_secondMoment
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Integrable f ν) (hf2 : Integrable (fun x => f x ^ 2) ν)
    {ε L M : ℝ} (hε : 0 ≤ ε) (hL : 0 < L)
    (hB : MeasurableSet {x | f x < -ε})
    (hM : (∫ x, f x ^ 2 ∂ν) ≤ M) :
    -ε - L * ν.real {x | f x < -ε} - M / L ≤ ∫ x, f x ∂ν := by
  let B := {x | f x < -ε}
  have hi : Integrable (B.indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_const 1).indicator hB
  have hpoint (x : X) :
      -f x ≤ ε + L * B.indicator (fun _ => (1 : ℝ)) x + f x ^ 2 / L := by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have hs := sq_nonneg (f x + L)
      have hd : -f x ≤ L + f x ^ 2 / L := by
        have ht : -f x * L ≤ L ^ 2 + f x ^ 2 := by nlinarith
        have hd := (le_div_iff₀ hL).mpr ht
        convert hd using 1
        field_simp
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      have hx' : -ε ≤ f x := le_of_not_gt hx
      have hp : 0 ≤ f x ^ 2 / L := div_nonneg (sq_nonneg _) hL.le
      nlinarith
  have h := integral_mono hf.neg
    (((integrable_const ε).add (hi.const_mul L)).add (hf2.div_const L)) hpoint
  change (∫ x, -f x ∂ν) ≤
    ∫ x, (ε + L * B.indicator (fun _ => (1 : ℝ)) x) + f x ^ 2 / L ∂ν at h
  rw [integral_add
      (f := fun x => ε + L * B.indicator (fun _ => (1 : ℝ)) x)
      (g := fun x => f x ^ 2 / L)
      ((integrable_const ε).add (hi.const_mul L)) (hf2.div_const L),
    integral_add (f := fun _ => ε)
      (g := fun x => L * B.indicator (fun _ => (1 : ℝ)) x)
      (integrable_const ε) (hi.const_mul L), integral_neg,
    integral_const_mul, integral_div] at h
  rw [integral_indicator_const (1 : ℝ) hB] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] at h
  have hm := div_le_div_of_nonneg_right hM hL.le
  linarith

/-- Dimension-dependent moments are also sufficient. The auxiliary weight
can grow exponentially, allowing polynomial moments to be combined with
exponential lower tails without a uniform second-moment estimate. -/
theorem integral_tendsto_zero_of_weighted_lowerTail_secondMoment
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)]
    (f : (n : ℕ) → X n → ℝ) (L M : ℕ → ℝ)
    (hnonpos : ∀ᶠ n : ℕ in atTop, ∀ x, f n x ≤ 0)
    (hL : ∀ᶠ n : ℕ in atTop, 0 < L n)
    (hmoment : ∀ᶠ n : ℕ in atTop,
      Integrable (f n) (ν n) ∧ Integrable (fun x => f n x ^ 2) (ν n) ∧
        (∫ x, f n x ^ 2 ∂ν n) ≤ M n)
    (hmeas : ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      MeasurableSet {x | f n x < -ε})
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => L n * (ν n).real {x | f n x < -ε}) atTop (𝓝 0))
    (hML : Tendsto (fun n => M n / L n) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂ν n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ht : ∀ᶠ n : ℕ in atTop,
      L n * (ν n).real {x | f n x < -(ε / 4)} < ε / 4 :=
    (htail (ε / 4) (by positivity)).eventually
      (Iio_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  have hm : ∀ᶠ n : ℕ in atTop, M n / L n < ε / 4 :=
    hML.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  apply eventually_atTop.mp
  filter_upwards [hnonpos, hL, hmoment, hmeas, ht, hm] with n hn hL hi hm ht hML
  have hlo := integral_nonpos_lower_bound_of_secondMoment (ν n) (f n)
    hi.1 hi.2.1 (by positivity : 0 ≤ ε / 4) hL (hm (ε / 4) (by positivity)) hi.2.2
  have hhi := integral_nonpos (μ := ν n) (hn : ∀ x, f n x ≤ 0)
  rw [Real.dist_eq, sub_zero, abs_of_nonpos hhi]
  linarith

/-- Lower-tail convergence and a bounded second moment remove a logarithmic
floor even when the probability spaces vary with dimension. -/
theorem integral_tendsto_zero_of_lowerTail_secondMoment
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)]
    (f : (n : ℕ) → X n → ℝ)
    (hnonpos : ∀ᶠ n : ℕ in atTop, ∀ x, f n x ≤ 0)
    (hmoment : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n : ℕ in atTop,
      Integrable (f n) (ν n) ∧ Integrable (fun x => f n x ^ 2) (ν n) ∧
        (∫ x, f n x ^ 2 ∂ν n) ≤ M)
    (hmeas : ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      MeasurableSet {x | f n x < -ε})
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (ν n).real {x | f n x < -ε}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂ν n) atTop (𝓝 0) := by
  obtain ⟨M, hM, hmoment⟩ := hmoment
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let L := 4 * (M + 1) / ε
  have hL : 0 < L := by dsimp [L]; positivity
  have hML : M / L < ε / 4 := by
    apply (div_lt_iff₀ hL).mpr
    dsimp [L]
    field_simp
    nlinarith
  have ht : Tendsto (fun n => L * (ν n).real {x | f n x < -(ε / 4)}) atTop (𝓝 0) := by
    simpa only [mul_zero] using (htail (ε / 4) (by positivity)).const_mul L
  have ht' : ∀ᶠ n : ℕ in atTop,
      L * (ν n).real {x | f n x < -(ε / 4)} < ε / 4 := by
    apply (ht.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).mono
    intro n hn
    simpa only [mul_zero] using hn
  apply eventually_atTop.mp
  filter_upwards [hnonpos, hmoment, hmeas, ht'] with n hn hi hm ht
  have hlo := integral_nonpos_lower_bound_of_secondMoment (ν n) (f n)
    hi.1 hi.2.1 (by positivity : 0 ≤ ε / 4) hL (hm (ε / 4) (by positivity)) hi.2.2
  have hhi := integral_nonpos (μ := ν n) (hn : ∀ x, f n x ≤ 0)
  rw [Real.dist_eq, sub_zero, abs_of_nonpos hhi]
  linarith

/-- The normalized logarithm of the actual conditional block probability,
with no exponential floor. -/
def untruncatedBlockLog (N k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ)
    (J : Disorder N μ.maxDegree) : ℝ :=
  Real.log (conditionalBlockProbability N k μ β q ρ J) / (N : ℝ)

/-- Uniform integrability required by the untruncated replica argument.
Positivity is retained explicitly to exclude `Real.log 0 = 0`. -/
def BlockLogSecondMoments (k : ℕ) (μ : FiniteMixture)
    (b : ℕ → ℝ) (q ρ : ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop,
    (∀ J, 0 < conditionalBlockProbability N k μ (b N) q ρ J) ∧
    Integrable (untruncatedBlockLog N k μ (b N) q ρ) (disorderLaw N μ.maxDegree) ∧
    Integrable (fun J => untruncatedBlockLog N k μ (b N) q ρ J ^ 2)
      (disorderLaw N μ.maxDegree) ∧
    (∫ J, untruncatedBlockLog N k μ (b N) q ρ J ^ 2
      ∂disorderLaw N μ.maxDegree) ≤ M

private theorem overlapBlock_measurable {N k : ℕ} (q ρ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) q ρ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem blockProbability_measurable (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : Measurable (conditionalBlockProbability N k μ β q ρ) := by
  exact (Kernel.measurable_coe _ (overlapBlock_measurable q ρ)).ennreal_toReal

/-- The expectation of the literal normalized block logarithm tends to
zero once its actual lower tails and second moments are controlled. -/
theorem untruncatedBlockLog_integral_tendsto
    (k : ℕ) (μ : FiniteMixture) (b : ℕ → ℝ) (q ρ : ℝ)
    (hmoment : BlockLogSecondMoments k μ b q ρ)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => blockLowerTailProbability N k μ (b N) q ρ ε)
        atTop (𝓝 0)) :
    Tendsto (fun N => ∫ J, untruncatedBlockLog N k μ (b N) q ρ J
      ∂disorderLaw N μ.maxDegree) atTop (𝓝 0) := by
  obtain ⟨M, hM, hmoment⟩ := hmoment
  have heq {N : ℕ} (hN : 1 ≤ N)
      (hp : ∀ J, 0 < conditionalBlockProbability N k μ (b N) q ρ J) (ε : ℝ) :
      {J | untruncatedBlockLog N k μ (b N) q ρ J < -ε} =
        {J | conditionalBlockProbability N k μ (b N) q ρ J <
          Real.exp (-ε * (N : ℝ))} := by
    ext J
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [mem_ofPred_eq, untruncatedBlockLog, div_lt_iff₀ hNr,
      Real.log_lt_iff_lt_exp (hp J)]
  apply integral_tendsto_zero_of_lowerTail_secondMoment
    (fun N => disorderLaw N μ.maxDegree) (fun N => untruncatedBlockLog N k μ (b N) q ρ)
  · filter_upwards [eventually_ge_atTop 1, hmoment] with N hN hmoment
    intro J
    apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg N)
    exact Real.log_nonpos (hmoment.1 J).le measureReal_le_one
  · exact ⟨M, hM, hmoment.mono fun _ h => h.2⟩
  · filter_upwards [eventually_ge_atTop 1, hmoment] with N hN hm
    intro ε _
    rw [heq hN hm.1]
    exact measurableSet_lt (blockProbability_measurable _ _ _ _ _ _) measurable_const
  · intro ε hε
    apply (htail ε hε).congr'
    filter_upwards [eventually_ge_atTop 1, hmoment] with N hN hm
    rw [heq hN hm.1]
    rfl


/-- The same untruncation step with dimension-dependent physical second
moments and weighted actual block lower tails. -/
theorem untruncatedBlockLog_integral_tendsto_of_weighted_tails
    (k : ℕ) (μ : FiniteMixture) (b : ℕ → ℝ) (q ρ : ℝ) (L M : ℕ → ℝ)
    (hL : ∀ᶠ N : ℕ in atTop, 0 < L N)
    (hmoment : ∀ᶠ N : ℕ in atTop,
      (∀ J, 0 < conditionalBlockProbability N k μ (b N) q ρ J) ∧
      Integrable (untruncatedBlockLog N k μ (b N) q ρ) (disorderLaw N μ.maxDegree) ∧
      Integrable (fun J => untruncatedBlockLog N k μ (b N) q ρ J ^ 2)
        (disorderLaw N μ.maxDegree) ∧
      (∫ J, untruncatedBlockLog N k μ (b N) q ρ J ^ 2
        ∂disorderLaw N μ.maxDegree) ≤ M N)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => L N * blockLowerTailProbability N k μ (b N) q ρ ε)
        atTop (𝓝 0))
    (hML : Tendsto (fun N => M N / L N) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ J, untruncatedBlockLog N k μ (b N) q ρ J
      ∂disorderLaw N μ.maxDegree) atTop (𝓝 0) := by
  have heq {N : ℕ} (hN : 1 ≤ N)
      (hp : ∀ J, 0 < conditionalBlockProbability N k μ (b N) q ρ J) (ε : ℝ) :
      {J | untruncatedBlockLog N k μ (b N) q ρ J < -ε} =
        {J | conditionalBlockProbability N k μ (b N) q ρ J <
          Real.exp (-ε * (N : ℝ))} := by
    ext J
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [mem_ofPred_eq, untruncatedBlockLog, div_lt_iff₀ hNr,
      Real.log_lt_iff_lt_exp (hp J)]
  apply integral_tendsto_zero_of_weighted_lowerTail_secondMoment
    (fun N => disorderLaw N μ.maxDegree) (fun N => untruncatedBlockLog N k μ (b N) q ρ) L M
  · filter_upwards [hmoment] with N hm
    intro J
    apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg N)
    exact Real.log_nonpos (hm.1 J).le measureReal_le_one
  · exact hL
  · exact hmoment.mono fun _ h => h.2
  · filter_upwards [eventually_ge_atTop 1, hmoment] with N hN hm
    intro ε _
    rw [heq hN hm.1]
    exact measurableSet_lt (blockProbability_measurable _ _ _ _ _ _) measurable_const
  · intro ε hε
    apply (htail ε hε).congr'
    filter_upwards [eventually_ge_atTop 1, hmoment] with N hN hm
    rw [heq hN hm.1]
    rfl
  · exact hML

private theorem band_measurable {N k : ℕ} (q δ ρ : ℝ) (m : Vector N) :
    MeasurableSet (ReplicatedBand k q δ ρ m) := by
  simp only [ReplicatedBand, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (isClosed_le (by unfold overlap; fun_prop) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem product_density_integrable {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Integrable (fun σ : Fin k → Vector N => ∏ i, gibbsDensity N β H (σ i))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) :=
  Integrable.fintype_prod (fun _ => gibbsDensity_integrable hN β hH)

private theorem product_gibbs_eq_withDensity {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Measure.pi (fun _ : Fin k => gibbsLaw N β H) =
      (Measure.pi (fun _ : Fin k => sphereLaw N)).withDensity
        (fun σ => ENNReal.ofReal (∏ i, gibbsDensity N β H (σ i))) := by
  let := gibbsLaw_probability hN β hH
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      (product_density_integrable (k := k) hN β hH).restrict
      (.of_forall (fun σ => Finset.prod_nonneg (fun i _ =>
        (gibbsDensity_pos hN β hH (σ i)).le))), Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      (gibbsDensity_pos hN β hH x).le))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gibbsLaw, withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (gibbsDensity_integrable hN β hH).restrict
      (.of_forall (fun x => (gibbsDensity_pos hN β hH x).le))]

private theorem product_gibbs_real_eq_integral {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    {B : Set (Fin k → Vector N)} (hB : MeasurableSet B) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β H)).real B =
      ∫ σ in B, ∏ i, gibbsDensity N β H (σ i)
        ∂Measure.pi (fun _ : Fin k => sphereLaw N) := by
  rw [product_gibbs_eq_withDensity hN β hH, Measure.real,
    withDensity_apply _ hB,
    ← ofReal_integral_eq_lintegral_ofReal
      (product_density_integrable (k := k) hN β hH).restrict
      (.of_forall (fun σ => Finset.prod_nonneg (fun i _ =>
        (gibbsDensity_pos hN β hH (σ i)).le))),
    ENNReal.toReal_ofReal (integral_nonneg (fun σ =>
      Finset.prod_nonneg (fun i _ => (gibbsDensity_pos hN β hH (σ i)).le)))]

private theorem product_density_formula {N k : ℕ} (β : ℝ)
    (H : Vector N → ℝ) (m : Vector N) (σ : Fin k → Vector N) :
    (∏ i, gibbsDensity N β H (σ i)) =
      (Real.exp ((k : ℝ) * β * H m) / partition N β H ^ k) *
        Real.exp (β * ∑ i : Fin k, (H (σ i) - H m)) := by
  simp only [gibbsDensity, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

private theorem product_gibbs_band_mass {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) :
    (Measure.pi (fun _ : Fin k => gibbsLaw N β (field (mixtureCoefficients μ) J))).real
        (ReplicatedBand k q δ ρ m) =
      (Real.exp ((k : ℝ) * β * field (mixtureCoefficients μ) J m) /
        mixturePartition μ β J ^ k) * replicatedBandPartition k μ β q δ ρ J m := by
  rw [product_gibbs_real_eq_integral hN β (field_contDiff _ J).continuous
    (band_measurable q δ ρ m)]
  simp_rw [product_density_formula β (field (mixtureCoefficients μ) J) m]
  rw [integral_const_mul]
  rfl


/-- At the zero center the literal band is exactly the overlap block. -/
theorem replicatedBand_zero_eq_overlapBlock {N : ℕ} (k : ℕ) (δ ρ : ℝ) :
    ReplicatedBand k 0 δ ρ (0 : Vector N) = overlapBlock 0 ρ := by
  ext σ
  simp [ReplicatedBand, overlapBlock, overlap]

/-- The exact untruncated finite-dimensional pressure identity. Positivity
of the actual Gibbs block is the only condition needed for the logarithm. -/
theorem replicatedBandPressure_zero_eq {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (μ : FiniteMixture) (β ρ : ℝ) (J : Disorder N μ.maxDegree)
    (hp : 0 < conditionalBlockProbability N k μ β 0 ρ J) :
    replicatedBandPressure k μ β 0 1 ρ J (0 : Vector N) =
      Real.log (mixturePartition μ β J) / (N : ℝ) -
        β * field (mixtureCoefficients μ) J 0 / (N : ℝ) +
        untruncatedBlockLog N k μ β 0 ρ J / (k : ℝ) := by
  have hmass := product_gibbs_band_mass (k := k) hN μ β 0 1 ρ J (0 : Vector N)
  have hcond : (Measure.pi (fun _ : Fin k =>
      gibbsLaw N β (field (mixtureCoefficients μ) J))).real
        (ReplicatedBand k 0 1 ρ (0 : Vector N)) =
      conditionalBlockProbability N k μ β 0 ρ J := by
    rw [replicatedBand_zero_eq_overlapBlock, conditionalBlockProbability,
      GaussianReplicaKernel.iid_apply, allDimensionGibbsKernel_apply]
  rw [hcond] at hmass
  have hZ := mixturePartition_pos hN μ β J
  have hfactor : 0 < Real.exp ((k : ℝ) * β *
      field (mixtureCoefficients μ) J 0) / mixturePartition μ β J ^ k := by positivity
  have hband : 0 < replicatedBandPartition k μ β 0 1 ρ J (0 : Vector N) := by
    have ht : 0 < (Real.exp ((k : ℝ) * β * field (mixtureCoefficients μ) J 0) /
        mixturePartition μ β J ^ k) *
        replicatedBandPartition k μ β 0 1 ρ J (0 : Vector N) := by rw [← hmass]; exact hp
    exact pos_of_mul_pos_right ht hfactor.le
  have hl := congrArg Real.log hmass
  rw [Real.log_mul hfactor.ne' hband.ne', Real.log_div (Real.exp_ne_zero _)
    (pow_ne_zero _ hZ.ne'), Real.log_exp, Real.log_pow] at hl
  unfold replicatedBandPressure untruncatedBlockLog
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hN0, hk0]
  nlinarith [hl]

/-- Expected zero-center pressure equals the ordinary quenched pressure
plus the actual normalized block cost. The field at the center has mean zero. -/
theorem expectedReplicatedBandPressure_zero_eq {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) (μ : FiniteMixture) (β ρ : ℝ)
    (hp : ∀ J, 0 < conditionalBlockProbability N k μ β 0 ρ J)
    (hi : Integrable (untruncatedBlockLog N k μ β 0 ρ) (disorderLaw N μ.maxDegree)) :
    expectedReplicatedBandPressure k μ β 0 1 ρ (0 : Vector N) =
      quenchedPressure N μ β +
        (∫ J, untruncatedBlockLog N k μ β 0 ρ J ∂disorderLaw N μ.maxDegree) / (k : ℝ) := by
  have hZ : Integrable (fun J : Disorder N μ.maxDegree =>
      Real.log (mixturePartition μ β J) / (N : ℝ)) (disorderLaw N μ.maxDegree) :=
    (sphericalLogPartition_integrable hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β).div_const _
  have hH := ((field_memLp (mixtureCoefficients μ) (0 : Vector N)).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul β
  unfold expectedReplicatedBandPressure
  simp_rw [replicatedBandPressure_zero_eq hN hk μ β ρ _ (hp _)]
  rw [integral_add
      (f := fun J => Real.log (mixturePartition μ β J) / (N : ℝ) -
        β * field (mixtureCoefficients μ) J 0 / (N : ℝ))
      (g := fun J => untruncatedBlockLog N k μ β 0 ρ J / (k : ℝ))
      (hZ.sub (hH.div_const (N : ℝ))) (hi.div_const (k : ℝ)),
    integral_sub (f := fun J => Real.log (mixturePartition μ β J) / (N : ℝ))
      (g := fun J => β * field (mixtureCoefficients μ) J 0 / (N : ℝ))
      hZ (hH.div_const (N : ℝ))]
  simp only [integral_div, integral_const_mul, field_mean, mul_zero, zero_div, sub_zero]
  rfl

/-- Lower tails and second moments imply the full zero-overlap replicated
pressure limit for an arbitrary temperature sequence having an ordinary
quenched-pressure limit. -/
theorem zero_expectedReplicatedBandPressure_tendsto
    (k : ℕ) (hk : 1 ≤ k) (μ : FiniteMixture) (b : ℕ → ℝ) (ρ F : ℝ)
    (hmoment : BlockLogSecondMoments k μ b 0 ρ)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => blockLowerTailProbability N k μ (b N) 0 ρ ε)
        atTop (𝓝 0))
    (hpressure : Tendsto (fun N => quenchedPressure N μ (b N)) atTop (𝓝 F)) :
    Tendsto (fun N => expectedReplicatedBandPressure k μ (b N) 0 1 ρ
      (0 : Vector N)) atTop (𝓝 F) := by
  have hc := (untruncatedBlockLog_integral_tendsto k μ b 0 ρ hmoment htail).div_const (k : ℝ)
  have ht := hpressure.add hc
  simp only [zero_div, add_zero] at ht
  apply ht.congr'
  obtain ⟨M, hM, hm⟩ := hmoment
  filter_upwards [eventually_ge_atTop 1, hm] with N hN hmoment
  exact (expectedReplicatedBandPressure_zero_eq hN hk μ (b N) ρ
    hmoment.1 hmoment.2.1).symm

/-- The actual transverse dimension correction causes no further loss:
the ambient-normalized pressure has the exact encoded residual limit. -/
theorem residualReplicatedPressure_tendsto_of_lowerTail_secondMoments
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    (hmoment : BlockLogSecondMoments k (physicalResidualMixture μ q hq)
      (dimensionCorrectedTemperature β 1) 0 ρ)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => blockLowerTailProbability N k (physicalResidualMixture μ q hq)
        (dimensionCorrectedTemperature β 1 N) 0 ρ ε) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) *
      expectedReplicatedBandPressure k (physicalResidualMixture μ q hq)
        (β * Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ))) 0 1 ρ (0 : Vector n))
      atTop (𝓝 (D.residual q)) := by
  let ν := physicalResidualMixture μ q hq
  let b := dimensionCorrectedTemperature β 1
  have hcost := (untruncatedBlockLog_integral_tendsto k ν b 0 ρ hmoment htail).div_const (k : ℝ)
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hterm := hratio.mul hcost
  simp only [zero_div, mul_zero] at hterm
  have hp := quenchedPressure_tendsto_dimensionCorrected_per_ambient_all_real ν 1
    (D.residual_limit q hq)
  have ht := hp.add hterm
  simp only [add_zero] at ht
  apply ht.congr'
  obtain ⟨M, hM, hm⟩ := hmoment
  filter_upwards [eventually_ge_atTop 1, hm] with N hN hm
  dsimp [b, ν, dimensionCorrectedTemperature]
  have he := expectedReplicatedBandPressure_zero_eq hN hk _ _ ρ hm.1 hm.2.1
  dsimp [dimensionCorrectedTemperature] at he
  rw [he, mul_add]

/-- A polynomial second-moment bound can be used directly with exponentially
small block lower tails. The hypotheses record only the two required weighted
limits and keep the actual residual mixture and transverse temperature. -/
theorem residualReplicatedPressure_tendsto_of_weighted_tails
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    (L M : ℕ → ℝ) (hL : ∀ᶠ N : ℕ in atTop, 0 < L N)
    (hmoment : ∀ᶠ N : ℕ in atTop,
      (∀ J, 0 < conditionalBlockProbability N k (physicalResidualMixture μ q hq)
        (dimensionCorrectedTemperature β 1 N) 0 ρ J) ∧
      Integrable (untruncatedBlockLog N k (physicalResidualMixture μ q hq)
        (dimensionCorrectedTemperature β 1 N) 0 ρ) (disorderLaw N (physicalResidualMixture μ q hq).maxDegree) ∧
      Integrable (fun J => untruncatedBlockLog N k (physicalResidualMixture μ q hq)
        (dimensionCorrectedTemperature β 1 N) 0 ρ J ^ 2)
        (disorderLaw N (physicalResidualMixture μ q hq).maxDegree) ∧
      (∫ J, untruncatedBlockLog N k (physicalResidualMixture μ q hq)
        (dimensionCorrectedTemperature β 1 N) 0 ρ J ^ 2
        ∂disorderLaw N (physicalResidualMixture μ q hq).maxDegree) ≤ M N)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => L N * blockLowerTailProbability N k (physicalResidualMixture μ q hq)
        (dimensionCorrectedTemperature β 1 N) 0 ρ ε) atTop (𝓝 0))
    (hML : Tendsto (fun N => M N / L N) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) *
      expectedReplicatedBandPressure k (physicalResidualMixture μ q hq)
        (β * Real.sqrt (((n + 1 : ℕ) : ℝ) / (n : ℝ))) 0 1 ρ (0 : Vector n))
      atTop (𝓝 (D.residual q)) := by
  let ν := physicalResidualMixture μ q hq
  let b := dimensionCorrectedTemperature β 1
  have hcost := (untruncatedBlockLog_integral_tendsto_of_weighted_tails
    k ν b 0 ρ L M hL hmoment htail hML).div_const (k : ℝ)
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hterm := hratio.mul hcost
  simp only [zero_div, mul_zero] at hterm
  have hp := quenchedPressure_tendsto_dimensionCorrected_per_ambient_all_real ν 1
    (D.residual_limit q hq)
  have ht := hp.add hterm
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1, hmoment] with N hN hm
  dsimp [b, ν, dimensionCorrectedTemperature]
  have he := expectedReplicatedBandPressure_zero_eq hN hk _ _ ρ hm.1 hm.2.1
  dsimp [dimensionCorrectedTemperature] at he
  rw [he, mul_add]

end SlowEquilibration.LiteratureSubagBandLowerResidual
