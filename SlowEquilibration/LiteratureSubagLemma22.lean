-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerComplete
public import SlowEquilibration.SphericalLogPartitionRegularity
public import SlowEquilibration.LiteratureSubagBandLowerTails
public import SlowEquilibration.SphericalNormalizedLikelihoodLowerTail
public import SlowEquilibration.GaussianNormConcentration
public import SlowEquilibration.SphericalSubcriticalOverlapMoment
public import SlowEquilibration.SphericalTemperatureStability

/-!
Steps toward Subag's Lemma 22 with the literal tensor disorder and mean
pressure. The pressure lower tails are proved up to and including the
static threshold in absolute inverse temperature.
Convexity of the physical log partition and a Gaussian minorant reduction
are also proved, as is the conditional transfer to corrected temperatures
at the full ambient rate. At arbitrary temperature the remaining analytic step is
the construction of sufficiently accurate minorants with vanishing
normalized Lipschitz scale (or the source's convex small-deviation and
superconcentration argument).

For the slab conclusion, the global pressure denominator is controlled at
a positive exponential rate and only the unnormalized slab events are
covered by the tuple net. Thus arbitrary-rate fixed unnormalized slab tails
imply exactly `UniformSlabLowerTails`, without asserting arbitrary-rate
tails for the normalized Gibbs mass. The codimension comparison needed to
obtain those fixed slab tails is not asserted here.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagLemma22

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagBandLowerComplete LiteratureSubagBandLowerProof
open LiteratureSubagBandLowerTails SourceLiteratureParisiTemperatureEven
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A Lipschitz lower approximation gives a lower tail even if the target
itself has a much larger Lipschitz constant. -/
theorem gaussian_lower_tail_of_lipschitz_minorant {ι : Type*} [Fintype ι]
    (f g : EuclideanSpace ℝ ι → ℝ) {L a ε t : ℝ} (hL : 0 ≤ L)
    (hg : LipschitzWith L.toNNReal g) (hminor : ∀ x, g x ≤ f x)
    (hmean : a - ε ≤ ∫ x, g x ∂SYK.standardGaussianMeasureOnEuclidean ι)
    (hεt : ε ≤ t) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real {x | f x < a - t} ≤
      Real.exp (-(t - ε) ^ 2 / (2 * L ^ 2)) := by
  have h := GaussianNormConcentration.centered_lipschitz_upper_tail
    (-g) hL hg.neg (sub_nonneg.mpr hεt)
  simp only [Pi.neg_apply, integral_neg] at h
  apply (measureReal_mono (fun x hx => ?_)).trans h
  change -(∫ y, g y ∂SYK.standardGaussianMeasureOnEuclidean ι) + (t - ε) ≤ -g x
  have hm := hminor x
  change f x < a - t at hx
  linarith

private theorem pressure_lower_tail_neg {N : ℕ} (μ : FiniteMixture) (β t : ℝ) :
    (disorderLaw N μ.maxDegree).real
      {J | Real.log (mixturePartition μ (-β) J) / (N : ℝ) <
        quenchedPressure N μ (-β) - t} =
    (disorderLaw N μ.maxDegree).real
      {J | Real.log (mixturePartition μ β J) / (N : ℝ) <
        quenchedPressure N μ β - t} := by
  have hE : MeasurableSet {J : Disorder N μ.maxDegree |
      Real.log (mixturePartition μ β J) / (N : ℝ) < quenchedPressure N μ β - t} :=
    measurableSet_lt ((partition_measurable (mixtureCoefficients μ) β).log.div_const _)
      measurable_const
  have h := (disorderLaw_neg_measurePreserving N μ.maxDegree).measure_preimage
    hE.nullMeasurableSet
  have heq : (MeasurableEquiv.neg (Disorder N μ.maxDegree) :
      Disorder N μ.maxDegree → Disorder N μ.maxDegree) = fun J => -J := rfl
  simpa only [Measure.real, heq, Set.preimage_ofPred_eq,
    mixturePartition_neg_beta, quenchedPressure_neg] using congrArg ENNReal.toReal h

/-- Sign reversal of the disorder extends the exact tail predicate to
negative temperatures without changing either rate or tolerance. -/
theorem pressureLowerTails_neg_iff (μ : FiniteMixture) (β : ℝ) :
    PressureLowerTails μ (-β) ↔ PressureLowerTails μ β := by
  unfold PressureLowerTails
  simp_rw [pressure_lower_tail_neg]

/-- At inverse temperature zero the pressure is deterministic, so every strict
lower-tail event is empty, including in dimension zero. -/
theorem pressureLowerTails_zero (μ : FiniteMixture) : PressureLowerTails μ 0 := by
  intro t c ht _
  apply Eventually.of_forall
  intro N
  have hE : {J : Disorder N μ.maxDegree |
      Real.log (mixturePartition μ 0 J) / (N : ℝ) < quenchedPressure N μ 0 - t} = ∅ := by
    ext J
    simp [quenchedPressure_zero, mixturePartition, partition, not_lt.mpr ht.le]
  rw [hE, measureReal_empty]
  exact (Real.exp_pos _).le

/-- Below the static threshold the existing truncated-feature support
bound gives Lemma 22 at every exponential rate, centered at the actual mean. -/
theorem pressureLowerTails_of_pos_lt_static (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) :
    PressureLowerTails μ β := by
  obtain ⟨C, K, hC, hK, htail⟩ := general_logPartition_lower_tail μ hβ hβs
  intro t c ht hc
  have hlarge : ∀ᶠ n : ℕ in atTop,
      C ≤ t * ((n + 1 : ℕ) : ℝ) / 2 ∧
        8 * K ^ 2 * c / t ^ 2 ≤ ((n + 1 : ℕ) : ℝ) := by
    have h₁ : Tendsto (fun n : ℕ => t * ((n + 1 : ℕ) : ℝ) / 2) atTop atTop :=
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_mul_atTop
        ht).atTop_div_const (by norm_num)
    exact (h₁.eventually_ge_atTop C).and
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop _)
  have hsucc : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n + 1) μ.maxDegree).real
        {J | Real.log (mixturePartition μ β J) / ((n + 1 : ℕ) : ℝ) <
          quenchedPressure (n + 1) μ β - t} ≤
            Real.exp (-c * ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [htail, hlarge] with n hn hlarge
    let M : ℝ := ((n + 1 : ℕ) : ℝ)
    have hM : 0 < M := by dsimp [M]; positivity
    have hmean := quenchedPressure_le_annealed (N := n + 1) (by omega) μ hβ
    have hsub : {J : Disorder (n + 1) μ.maxDegree |
        Real.log (mixturePartition μ β J) / M < quenchedPressure (n + 1) μ β - t} ⊆
        {J | Real.log (mixturePartition μ β J) ≤
          annealedExponent (n + 1) (mixtureCoefficients μ) β - C - K * (t * M / (2 * K))} := by
      intro J hJ
      have hj := (div_lt_iff₀ hM).mp hJ
      have hm := mul_le_mul_of_nonneg_right hmean hM.le
      have hcancel : K * (t * M / (2 * K)) = t * M / 2 := by field_simp
      rw [hcancel]
      unfold annealedExponent
      rw [covariancePolynomial_mixture]
      change Real.log (mixturePartition μ β J) ≤
        M * β ^ 2 * μ.xi 1 / 2 - C - t * M / 2
      calc
        _ ≤ (quenchedPressure (n + 1) μ β - t) * M := hj.le
        _ ≤ (β ^ 2 * μ.xi 1 / 2 - t) * M := by gcongr
        _ ≤ _ := by nlinarith only [hlarge.1]
    have hrate : c * M ≤ (t * M / (2 * K)) ^ 2 / 2 := by
      have hh := (div_le_iff₀ (sq_pos_of_pos ht)).mp hlarge.2
      have hm := mul_le_mul_of_nonneg_right hh hM.le
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hK))).mpr
      nlinarith
    exact (measureReal_mono hsub).trans ((hn _ (by positivity)).trans
      (Real.exp_le_exp.mpr (by linarith)))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hsucc
  filter_upwards [eventually_ge_atTop (n₀ + 1)] with N hN
  cases N with
  | zero => omega
  | succ n => exact hn₀ n (by omega)

/-- Lemma 22 holds for either sign strictly below the static threshold.
The all-temperature conclusion is not claimed by this theorem. -/
theorem pressureLowerTails_of_abs_lt_static (μ : FiniteMixture) {β : ℝ}
    (hβs : |β| < Thresholds.staticThreshold μ.xi) : PressureLowerTails μ β := by
  rcases lt_trichotomy β 0 with hβ | hβ | hβ
  · have h := pressureLowerTails_of_pos_lt_static μ (neg_pos.mpr hβ)
      (by simpa only [abs_of_neg hβ] using hβs)
    exact (pressureLowerTails_neg_iff μ β).mp h
  · subst β
    exact pressureLowerTails_zero μ
  · exact pressureLowerTails_of_pos_lt_static μ hβ
      (by simpa only [abs_of_pos hβ] using hβs)

/-- Temperature convexity compares the actual partitions on the same
disorder sample, for every real starting temperature. -/
theorem logPartition_temperature_scaling_le {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {scale : ℝ} (hscale : 1 ≤ scale) :
    scale * Real.log (mixturePartition μ β J) ≤ Real.log (mixturePartition μ (scale * β) J) := by
  have hscale0 : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hf := GaussianSpinInterpolation.logPartition_line_convex (sphereLaw N)
    (sphereLinear (mixtureCoefficients μ)) (sphereLinear_measurable _)
    (Real.sqrt_nonneg _) (sphereLinear_bound hN _ (mixtureCoefficients_nonnegative μ))
    0 (euclideanDisorder J)
  have hc : ConvexOn ℝ univ (fun b => Real.log (mixturePartition μ b J)) := by
    change ConvexOn ℝ univ (fun b =>
      Real.log (partition N b (field (mixtureCoefficients μ) J)))
    simpa only [zero_add, GaussianSpinInterpolation.logPartition,
      gaussianMoment_eq_partition, unpack_euclideanDisorder] using hf
  have ha : 0 ≤ 1 - 1 / scale := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hscale0).mpr (by simpa using hscale)
  have h := hc.2 (mem_univ (0 : ℝ)) (mem_univ (scale * β)) ha
    (show 0 ≤ 1 / scale by positivity) (by ring)
  have heq : (1 - 1 / scale) • (0 : ℝ) + (1 / scale) • (scale * β) = β := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    field_simp
  rw [heq] at h
  change Real.log (mixturePartition μ β J) ≤
    (1 - 1 / scale) • Real.log (mixturePartition μ 0 J) +
      (1 / scale) • Real.log (mixturePartition μ (scale * β) J) at h
  have hz : Real.log (mixturePartition μ 0 J) = 0 := by simp [mixturePartition, partition]
  rw [hz] at h
  simp only [smul_eq_mul, mul_zero, zero_add] at h
  have hh := mul_le_mul_of_nonneg_left h hscale0.le
  convert hh using 1; field_simp

/-- Uniform temperature continuity and convexity transfer arbitrary-rate
lower tails from positive temperatures approaching the target from below. -/
theorem pressureLowerTails_of_left_approximation (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 < β)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ b : ℝ,
      0 < b ∧ b ≤ β ∧ β - b < ε ∧ PressureLowerTails μ b) :
    PressureLowerTails μ β := by
  intro t c ht hc
  let C := 2 * β * μ.xi 1
  have hC : 0 < C := by dsimp [C]; positivity [μ.xi_pos (show (0 : ℝ) < 1 by norm_num)]
  obtain ⟨b, hb, hbβ, hclose, htail⟩ := happrox (t / (2 * C)) (by positivity)
  let scale := β / b
  have hscale : 1 ≤ scale := (le_div_iff₀ hb).mpr (by simpa using hbβ)
  have hscale0 : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hgap : C * (β - b) < t / 2 := by
    have h := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp hclose
    linarith
  filter_upwards [htail (t / (2 * scale)) c (by positivity) hc,
    eventually_ge_atTop (1 : ℕ)] with N htail hN
  apply (measureReal_mono (fun J hJ => ?_)).trans htail
  have hscale := logPartition_temperature_scaling_le hN μ J b hscale
  have heq : scale * b = β := by dsimp [scale]; exact div_mul_cancel₀ _ hb.ne'
  rw [heq] at hscale
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsample : scale * (Real.log (mixturePartition μ b J) / (N : ℝ)) ≤
      Real.log (mixturePartition μ β J) / (N : ℝ) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hscale hNr.le
  have hmean := quenchedPressure_temperature_lipschitz hN μ
    (show β ∈ Icc 0 β from ⟨hβ.le, le_rfl⟩) (show b ∈ Icc 0 β from ⟨hb.le, hbβ⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr hbβ)] at hmean
  have hnonneg := (quenchedPressure_mem_annealed_interval hN μ hb.le).1
  have hm : quenchedPressure N μ β - scale * quenchedPressure N μ b < t / 2 := by
    have h := (le_abs_self (quenchedPressure N μ β - quenchedPressure N μ b)).trans hmean
    change _ ≤ C * (β - b) at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) hnonneg]
  change Real.log (mixturePartition μ β J) / (N : ℝ) < quenchedPressure N μ β - t at hJ
  change Real.log (mixturePartition μ b J) / (N : ℝ) <
    quenchedPressure N μ b - t / (2 * scale)
  have he : quenchedPressure N μ b - t / (2 * scale) =
      (quenchedPressure N μ b * scale - t / 2) / scale := by field_simp
  rw [he]
  apply (lt_div_iff₀ hscale0).mpr
  nlinarith

/-- The exact Lemma 22 predicate holds up to and including the static
threshold, for both signs of the temperature, without Chen's formula. -/
theorem pressureLowerTails_of_abs_le_static (μ : FiniteMixture) {β : ℝ}
    (hβs : |β| ≤ Thresholds.staticThreshold μ.xi) : PressureLowerTails μ β := by
  have hpos : ∀ b : ℝ, 0 < b → b ≤ Thresholds.staticThreshold μ.xi →
      PressureLowerTails μ b := by
    intro b hb hbs
    apply pressureLowerTails_of_left_approximation μ hb
    intro ε hε
    let δ := min (b / 2) (ε / 2)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδb : δ ≤ b / 2 := min_le_left _ _
    have hδε : δ ≤ ε / 2 := min_le_right _ _
    refine ⟨b - δ, by linarith, by linarith, by linarith, ?_⟩
    exact pressureLowerTails_of_pos_lt_static μ (by linarith) (by linarith)
  rcases lt_trichotomy β 0 with hβ | hβ | hβ
  · exact (pressureLowerTails_neg_iff μ β).mp
      (hpos (-β) (neg_pos.mpr hβ) (by simpa only [abs_of_neg hβ] using hβs))
  · subst β
    exact pressureLowerTails_zero μ
  · exact hpos β hβ (by simpa only [abs_of_pos hβ] using hβs)

/-- Fixed-temperature arbitrary-rate tails transport to the physical
codimension correction, with the exponent and pressure both normalized by
the ambient dimension. The supplied pressure limit may be obtained from
Chen's formula or from physical thermodynamic data. -/
theorem dimensionCorrected_pressure_lower_tails_of_limit
    (μ : FiniteMixture) (β F : ℝ) (j : ℕ) (htail : PressureLowerTails μ β)
    (hlimit : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 F)) :
    ∀ t c : ℝ, 0 < t → 0 < c → ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real
        {J | Real.log (mixturePartition μ (dimensionCorrectedTemperature β j N) J) /
          ((N + j : ℕ) : ℝ) < F - t} ≤ Real.exp (-c * ((N + j : ℕ) : ℝ)) := by
  intro t c ht hc
  have hr : Tendsto (fun N : ℕ => (N : ℝ) / ((N + j : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add] using tendsto_natCast_div_add_atTop (j : ℝ)
  have hs : Tendsto (fun N : ℕ => Real.sqrt (((N + j : ℕ) : ℝ) / (N : ℝ)))
      atTop (𝓝 1) := by
    have h := dimensionCorrectedTemperature_tendsto 1 j
    change Tendsto (fun N : ℕ => 1 * Real.sqrt (((N + j : ℕ) : ℝ) / (N : ℝ)))
      atTop (𝓝 1) at h
    simpa only [one_mul] using h
  have hm := (hr.mul hs).mul (hlimit.sub_const (t / 2))
  simp only [one_mul] at hm
  have hnear := hm.eventually (Ioi_mem_nhds (show F - t < F - t / 2 by linarith))
  filter_upwards [htail (t / 2) (2 * c) (half_pos ht) (by positivity), hnear,
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop j] with N htail hnear hN hNj
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hMr : 0 < ((N + j : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  let scale := Real.sqrt (((N + j : ℕ) : ℝ) / (N : ℝ))
  let a := ((N : ℝ) / ((N + j : ℕ) : ℝ)) * scale
  have hscale : 1 ≤ scale := by
    apply Real.one_le_sqrt.mpr
    apply (le_div_iff₀ hNr).mpr
    simp only [one_mul, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg j)
  have ha : 0 ≤ a := by dsimp [a, scale]; positivity
  have hsub : {J : Disorder N μ.maxDegree |
      Real.log (mixturePartition μ (dimensionCorrectedTemperature β j N) J) /
        ((N + j : ℕ) : ℝ) < F - t} ⊆
      {J | Real.log (mixturePartition μ β J) / (N : ℝ) < quenchedPressure N μ β - t / 2} := by
    intro J hJ
    have hh := logPartition_temperature_scaling_le hN μ J β hscale
    have heq : scale * β = dimensionCorrectedTemperature β j N := by
      simp only [dimensionCorrectedTemperature, scale, mul_comm]
    rw [heq] at hh
    have hsample := div_le_div_of_nonneg_right hh hMr.le
    have he : scale * Real.log (mixturePartition μ β J) / ((N + j : ℕ) : ℝ) =
        a * (Real.log (mixturePartition μ β J) / (N : ℝ)) := by
      dsimp [a]
      field_simp
    rw [he] at hsample
    change _ < _
    by_contra hnot
    have hl := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) ha
    change F - t < a * (quenchedPressure N μ β - t / 2) at hnear
    change Real.log (mixturePartition μ (dimensionCorrectedTemperature β j N) J) /
      ((N + j : ℕ) : ℝ) < F - t at hJ
    linarith
  have hrate : -(2 * c) * (N : ℝ) ≤ -c * ((N + j : ℕ) : ℝ) := by
    have hj : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNj
    rw [Nat.cast_add]
    nlinarith
  exact (measureReal_mono hsub).trans (htail.trans (Real.exp_le_exp.mpr hrate))

/-- A construction of uniformly accurate Gaussian minorants whose
normalized Lipschitz scale tends to zero would give the full Lemma 22.
The functions are minorants of the literal pressure, and the mean gap is
measured against the actual finite-dimensional quenched expectation. -/
theorem pressureLowerTails_of_lipschitz_minorants (μ : FiniteMixture) (β : ℝ)
    (g : (N : ℕ) → EuclideanDisorder N μ.maxDegree → ℝ) (L : ℕ → ℝ)
    (hL : ∀ N, 0 < L N) (hg : ∀ N, LipschitzWith (L N).toNNReal (g N))
    (hminor : ∀ N x, g N x ≤
      logPartitionEuclidean (mixtureCoefficients μ) β x / (N : ℝ))
    (hmean : Tendsto (fun N => quenchedPressure N μ β -
      ∫ x, g N x ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree))
        atTop (𝓝 0))
    (hscale : Tendsto (fun N : ℕ => (N : ℝ) * (L N) ^ 2) atTop (𝓝 0)) :
    PressureLowerTails μ β := by
  intro t c ht hc
  have hm := hmean.eventually_lt_const (half_pos ht)
  have hs := hscale.eventually_lt_const
    (show 0 < t ^ 2 / (8 * c) by positivity)
  filter_upwards [hm, hs, eventually_ge_atTop (1 : ℕ)] with N hm hs hN
  have hLN := hL N
  let f := fun x : EuclideanDisorder N μ.maxDegree =>
    logPartitionEuclidean (mixtureCoefficients μ) β x / (N : ℝ)
  have hminor' : ∀ x, g N x ≤ f x := hminor N
  have hh := gaussian_lower_tail_of_lipschitz_minorant f (g N) (hL N).le (hg N)
    hminor' (a := quenchedPressure N μ β) (ε := t / 2) (t := t)
    (by linarith) (by linarith)
  have hLip := logPartitionEuclidean_lipschitz_all_real hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) β
  have hE : MeasurableSet {x : EuclideanDisorder N μ.maxDegree |
      f x < quenchedPressure N μ β - t} :=
    measurableSet_lt (hLip.continuous.measurable.div_const _) measurable_const
  rw [← (euclideanDisorder_hasLaw N μ.maxDegree).measureReal_eq hE] at hh
  have hrate : c * (N : ℝ) ≤ (t - t / 2) ^ 2 / (2 * (L N) ^ 2) := by
    have hs' := (lt_div_iff₀ (show 0 < 8 * c by positivity)).mp hs
    apply (le_div_iff₀ (show 0 < 2 * (L N) ^ 2 by positivity)).mpr
    nlinarith
  exact hh.trans (Real.exp_le_exp.mpr (by
    simpa only [neg_div, neg_mul] using neg_le_neg hrate))

/-- The global partition denominator has a positive exponential upper-tail
rate at every real temperature. The harmless enlargement of the Lipschitz
constant includes zero temperature in the same formula. -/
theorem pressureUpperTailProbability_le {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) {t : ℝ} (ht : 0 < t) :
    (disorderLaw N μ.maxDegree).real (pressureUpperTailEvent N μ β t) ≤
      Real.exp (-(t ^ 2 / (2 * (|β| + 1) ^ 2 * μ.xi 1)) * (N : ℝ)) := by
  let F := logPartitionEuclidean (N := N) (mixtureCoefficients μ) β
  let L := (|β| + 1) * Real.sqrt ((N : ℝ) * μ.xi 1)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hxi : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  have hL : 0 < L := by dsimp [L]; positivity
  have hLip : LipschitzWith L.toNNReal F := by
    have h := logPartitionEuclidean_lipschitz_all_real hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β
    rw [covariancePolynomial_mixture] at h
    apply h.weaken
    apply Real.toNNReal_le_toNNReal
    dsimp [L]
    nlinarith [Real.sqrt_nonneg ((N : ℝ) * μ.xi 1)]
  have hmean : (∫ J : Disorder N μ.maxDegree, Real.log (mixturePartition μ β J)
      ∂disorderLaw N μ.maxDegree) =
      ∫ x, F x ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree) :=
    (euclideanDisorder_hasLaw N μ.maxDegree).integral_comp
      hLip.continuous.aestronglyMeasurable
  have hh := GaussianNormConcentration.centered_lipschitz_upper_tail F hL.le hLip
    (mul_nonneg hNr.le ht.le)
  have hE : MeasurableSet {x : EuclideanDisorder N μ.maxDegree |
      (∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) +
        (N : ℝ) * t ≤ F x} := measurableSet_le measurable_const hLip.continuous.measurable
  rw [← (euclideanDisorder_hasLaw N μ.maxDegree).measureReal_eq hE, ← hmean] at hh
  have hsub : pressureUpperTailEvent N μ β t ⊆
      {J | (∫ K : Disorder N μ.maxDegree, Real.log (mixturePartition μ β K)
        ∂disorderLaw N μ.maxDegree) + (N : ℝ) * t ≤ F (euclideanDisorder J)} := by
    intro J hJ
    change quenchedPressure N μ β + t < Real.log (mixturePartition μ β J) / (N : ℝ) at hJ
    have h := (lt_div_iff₀ hNr).mp hJ
    change (∫ K, Real.log (mixturePartition μ β K) ∂disorderLaw N μ.maxDegree) +
      (N : ℝ) * t ≤ Real.log (mixturePartition μ β J)
    unfold quenchedPressure at h
    rw [add_mul, div_mul_cancel₀ _ hNr.ne'] at h
    linarith
  have hsq : L ^ 2 = (|β| + 1) ^ 2 * (N : ℝ) * μ.xi 1 := by
    dsimp [L]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hNr.le hxi.le)]
    ring
  have hrate : -((N : ℝ) * t) ^ 2 / (2 * L ^ 2) =
      -(t ^ 2 / (2 * (|β| + 1) ^ 2 * μ.xi 1)) * (N : ℝ) := by
    rw [hsq]
    field_simp
  exact (measureReal_mono hsub).trans (hh.trans_eq (by rw [hrate]))

private theorem prefactor_exp_eventually_le {A d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop,
      A * Real.exp (-d * (N : ℝ)) ≤ Real.exp (-(d / 2) * (N : ℝ)) := by
  have hlim : Tendsto (fun N : ℕ => A * Real.exp (-(d / 2) * (N : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith : -(d / 2) < 0))
    simpa only [Function.comp_apply, mul_zero] using he.const_mul A
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hN
  calc
    A * Real.exp (-d * (N : ℝ)) =
        (A * Real.exp (-(d / 2) * (N : ℝ))) * Real.exp (-(d / 2) * (N : ℝ)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by nlinarith [Real.exp_pos (-(d / 2) * (N : ℝ))]

/-- Arbitrary-rate fixed unnormalized slab tails imply precisely the
positive-rate uniform Gibbs slab predicate. The denominator is handled
once, before the exponential tuple-net union bound. -/
theorem uniformSlabLowerTails_of_fixed_partition_tails (μ : FiniteMixture) (β : ℝ)
    (hfixed : ∀ j : ℕ, ∀ η t c : ℝ, 0 < η → 0 < t → 0 < c →
      ∀ᶠ N : ℕ in atTop, ∀ σ : Fin j → Vector N,
        (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
          (disorderLaw N μ.maxDegree).real (fixedSlabPartitionLowerTailEvent μ β η t σ) ≤
            Real.exp (-c * (N : ℝ))) :
    UniformSlabLowerTails μ β := by
  intro j ρ t hρ ht
  let d := (t / 2) ^ 2 / (2 * (|β| + 1) ^ 2 * μ.xi 1)
  have hd : 0 < d := by dsimp [d]; positivity [μ.xi_pos (show (0 : ℝ) < 1 by norm_num)]
  have hη : 0 < ρ / 2 := half_pos hρ
  have hlog : 0 ≤ Real.log (1 + 2 / (ρ / 2)) := Real.log_nonneg (by
    have : 0 ≤ 2 / (ρ / 2) := by positivity
    linarith)
  have hc : 0 < d + (j : ℝ) * Real.log (1 + 2 / (ρ / 2)) := by positivity
  refine ⟨d / 2, half_pos hd, ?_⟩
  filter_upwards [hfixed j (ρ / 2) (t / 2) _ hη (half_pos ht) hc,
    prefactor_exp_eventually_le (A := 2) hd, eventually_ge_atTop (1 : ℕ)]
      with N hfixed hsum hN
  have hh := uniformSlabLowerTailProbability_le_exp_add_pressureUpper
    (j := j) (ρ := ρ) (η := ρ / 2) (θ := ρ / 2) hN μ β t d
    hη (show ρ / 2 + ρ / 2 ≤ ρ by linarith) hfixed
  have hu := pressureUpperTailProbability_le hN μ β (half_pos ht)
  calc
    _ ≤ (disorderLaw N μ.maxDegree).real (pressureUpperTailEvent N μ β (t / 2)) +
        Real.exp (-d * (N : ℝ)) := hh
    _ ≤ Real.exp (-d * (N : ℝ)) + Real.exp (-d * (N : ℝ)) := add_le_add hu le_rfl
    _ = 2 * Real.exp (-d * (N : ℝ)) := by ring
    _ ≤ _ := hsum

/-- Every fixed number of spherical slab constraints leaves at least half
of the uniform sphere mass eventually, uniformly over their directions. -/
theorem uniformSphereSlab_mass_eventually_lower (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop, ∀ σ : Fin j → Vector N,
      (∀ i, ‖σ i‖ ^ 2 = (N : ℝ)) →
        (1 / 2 : ℝ) ≤ (sphereLaw N).real {y | ∀ i, |overlap y (σ i)| < ρ} := by
  obtain ⟨C, hC, hmoment⟩ := sphere_overlap_exp_square_eventually_bounded
    (b := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hd : 0 < ρ ^ 2 / 4 := by positivity
  have hlim : Tendsto (fun N : ℕ => (j : ℝ) * C * Real.exp (-(ρ ^ 2 / 4) * (N : ℝ)))
      atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hd))
    simpa only [Function.comp_apply, mul_zero] using he.const_mul ((j : ℝ) * C)
  filter_upwards [hmoment, hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℕ)] with N hmoment hsmall hN
  intro σ hσ
  let bad : Fin j → Set (Vector N) := fun i => {y | ρ ≤ |overlap y (σ i)|}
  have hbad (i : Fin j) : MeasurableSet (bad i) := by
    apply measurableSet_le measurable_const
    unfold overlap
    fun_prop
  have htail (i : Fin j) :
      (sphereLaw N).real (bad i) ≤ C * Real.exp (-(ρ ^ 2 / 4) * (N : ℝ)) := by
    let W : Vector N → ℝ := fun y => Real.exp ((1 / 4 : ℝ) * (N : ℝ) * (overlap (σ i) y) ^ 2)
    let A : ℝ := Real.exp ((1 / 4 : ℝ) * (N : ℝ) * ρ ^ 2)
    have hA : 0 < A := Real.exp_pos _
    have hi : Integrable W (sphereLaw N) := integrable_sphere_of_continuous hN (by
      dsimp [W]
      unfold overlap
      fun_prop)
    have hm := mul_meas_ge_le_integral_of_nonneg
      (show 0 ≤ᵐ[sphereLaw N] W from .of_forall (fun _ => (Real.exp_pos _).le)) hi A
    have hsub : bad i ⊆ {y | A ≤ W y} := by
      intro y hy
      have hy' : ρ ≤ |overlap (σ i) y| := by
        simpa only [bad, mem_ofPred_eq, overlap, real_inner_comm] using hy
      have hs : ρ ^ 2 ≤ (overlap (σ i) y) ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ hρ.le (abs_nonneg _)).mpr hy'
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    have hm' : A * (sphereLaw N).real (bad i) ≤ C :=
      (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hA.le).trans
        (hm.trans (hmoment (σ i) (hσ i)))
    calc
      _ ≤ C / A := (le_div_iff₀ hA).mpr (by nlinarith only [hm'])
      _ = _ := by
        dsimp [A]
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring
  have hU : (sphereLaw N).real (⋃ i, bad i) ≤
      (j : ℝ) * C * Real.exp (-(ρ ^ 2 / 4) * (N : ℝ)) := by
    calc
      _ ≤ ∑ i : Fin j, (sphereLaw N).real (bad i) := measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _i : Fin j, C * Real.exp (-(ρ ^ 2 / 4) * (N : ℝ)) :=
        Finset.sum_le_sum (fun i _ => htail i)
      _ = _ := by simp [mul_assoc]
  have heq : {y | ∀ i, |overlap y (σ i)| < ρ} = (⋃ i, bad i)ᶜ := by
    ext y
    simp [bad, not_le]
  rw [heq, measureReal_compl (MeasurableSet.iUnion hbad), probReal_univ]
  linarith

/-- At inverse temperature zero the uniform slab failure event is empty eventually.
In particular the exact uniform predicate holds, with no pressure premise. -/
theorem uniformSlabLowerTails_zero (μ : FiniteMixture) : UniformSlabLowerTails μ 0 := by
  intro j ρ t hρ ht
  have hlim : Tendsto (fun N : ℕ => Real.exp (-t * (N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos ht))
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [uniformSphereSlab_mass_eventually_lower j hρ,
    hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hmass hsmall
  have hE : uniformSlabLowerTailEvent N j μ 0 ρ t = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro J hJ
    apply hJ
    intro σ hσ _
    have hzero : gibbsLaw N 0 (fieldOfMixture μ J) = sphereLaw N := by
      simp [gibbsLaw, gibbsDensity, partition]
    rw [hzero]
    exact hsmall.le.trans (hmass σ hσ)
  rw [uniformSlabLowerTailProbability, hE, measureReal_empty]
  exact (Real.exp_pos _).le

end SlowEquilibration.LiteratureSubagLemma22
