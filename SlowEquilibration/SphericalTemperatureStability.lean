-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianInterpolation
public import SlowEquilibration.SphericalGuerraBound
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # Actual quenched-pressure stability under varying temperature

The genuine Gibbs-replica derivative and spherical overlap bound give a
dimension-independent Lipschitz estimate. A fixed-temperature limit therefore
transports to convergent temperature sequences, including sequences approaching
a static endpoint from above.
-/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Nonnegative tensor coefficients control the absolute covariance at every
signed spherical overlap; no parity condition is needed. -/
theorem abs_covariancePolynomial_le_at_one {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {r : ℝ} (hr : |r| ≤ 1) :
    |covariancePolynomial c r| ≤ covariancePolynomial c 1 := by
  unfold covariancePolynomial
  calc
    |∑ p, c p * r ^ (p : ℕ)| ≤ ∑ p, |c p * r ^ (p : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, c p * 1 ^ (p : ℕ) := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul, abs_of_nonneg (hc p), abs_pow, one_pow, mul_one]
      exact mul_le_of_le_one_right (hc p) (pow_le_one₀ (abs_nonneg _) hr)

/-- The literal independent-replica covariance is bounded by the diagonal
covariance, uniformly in disorder and dimension. -/
theorem abs_replicaCovariance_le_at_one {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (g : EuclideanDisorder N P) :
    |replicaCovariance c β g| ≤ covariancePolynomial c 1 := by
  let G := gibbsLaw N β (field c (unpackDisorder g))
  let _ : IsProbabilityMeasure G :=
    gibbsLaw_probability hN β (field_contDiff c _).continuous
  have hs : ∀ᵐ z : Vector N × Vector N ∂G.prod G,
      ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (by
      exact (isClosed_eq (continuous_fst.norm.pow 2) continuous_const).measurableSet.inter
        (isClosed_eq (continuous_snd.norm.pow 2) continuous_const).measurableSet)).mpr
    filter_upwards [gibbsLaw_support hN β (field c (unpackDisorder g))] with x hx
    filter_upwards [gibbsLaw_support hN β (field c (unpackDisorder g))] with y hy
    exact ⟨hx, hy⟩
  have hb : ∀ᵐ z : Vector N × Vector N ∂G.prod G,
      ‖covariancePolynomial c (overlap z.1 z.2)‖ ≤ covariancePolynomial c 1 := by
    filter_upwards [hs] with z hz
    rw [Real.norm_eq_abs]
    exact abs_covariancePolynomial_le_at_one c hc
      (abs_le.mpr (overlap_mem_Icc_of_norm_sq hN _ _ hz.1 hz.2))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one, replicaCovariance, G] using
    norm_integral_le_of_norm_le_const hb

/-- The actual averaged replica term is bounded by ξ(1). -/
theorem abs_mean_replicaCovariance_le {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    |∫ g : EuclideanDisorder N μ.maxDegree,
      replicaCovariance (mixtureCoefficients μ) β g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)| ≤ μ.xi 1 := by
  have hb : ∀ᵐ g : EuclideanDisorder N μ.maxDegree
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree),
      ‖replicaCovariance (mixtureCoefficients μ) β g‖ ≤ μ.xi 1 :=
    .of_forall fun g => by
      rw [Real.norm_eq_abs]
      simpa only [covariancePolynomial_mixture] using
        abs_replicaCovariance_le_at_one hN (mixtureCoefficients μ)
          (mixtureCoefficients_nonnegative μ) β g
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

/-- A dimension-independent bound on the genuine ordinary derivative. -/
theorem abs_quenchedPressure_deriv_le {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    {B β : ℝ} (hβ : β ∈ Icc 0 B) :
    |deriv (quenchedPressure N μ) β| ≤ 2*B*μ.xi 1 := by
  rw [quenchedPressure_deriv_replicaCovariance hN μ β, abs_mul, abs_of_nonneg hβ.1]
  have hx := (μ.xi_pos (show (0 : ℝ) < 1 by norm_num)).le
  have hr := abs_mean_replicaCovariance_le hN μ β
  have hdiff : |μ.xi 1 - ∫ g : EuclideanDisorder N μ.maxDegree,
      replicaCovariance (mixtureCoefficients μ) β g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)| ≤ 2*μ.xi 1 := by
    calc
      _ ≤ |μ.xi 1| + |∫ g : EuclideanDisorder N μ.maxDegree,
        replicaCovariance (mixtureCoefficients μ) β g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)| := abs_sub _ _
      _ ≤ 2*μ.xi 1 := by rw [abs_of_nonneg hx]; linarith
  calc
    _ ≤ β*(2*μ.xi 1) := mul_le_mul_of_nonneg_left hdiff hβ.1
    _ ≤ 2*B*μ.xi 1 := by nlinarith [mul_le_mul_of_nonneg_right hβ.2 hx]

/-- Actual finite-volume pressure is uniformly Lipschitz on a bounded
nonnegative temperature interval. -/
theorem quenchedPressure_temperature_lipschitz {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {B β γ : ℝ} (hβ : β ∈ Icc 0 B) (hγ : γ ∈ Icc 0 B) :
    |quenchedPressure N μ β - quenchedPressure N μ γ| ≤
      (2*B*μ.xi 1)*|β-γ| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Icc 0 B).norm_image_sub_le_of_norm_deriv_le
      (fun b _ => quenchedPressure_differentiable hN μ b)
      (fun b hb => by simpa only [Real.norm_eq_abs] using
        abs_quenchedPressure_deriv_le hN μ hb) hγ hβ

/-- Any genuine fixed-temperature pressure limit transports to arbitrary
convergent nonnegative temperatures. The temperatures need not remain in an
RS region. -/
theorem quenchedPressure_tendsto_varying_temperature (μ : FiniteMixture)
    (D : ℕ → ℕ) (b : ℕ → ℝ) {β F : ℝ} (hβ : 0 ≤ β)
    (hD : ∀ᶠ n in atTop, 1 ≤ D n) (hb0 : ∀ᶠ n in atTop, 0 ≤ b n)
    (hb : Tendsto b atTop (𝓝 β))
    (hfixed : Tendsto (fun n => quenchedPressure (D n) μ β) atTop (𝓝 F)) :
    Tendsto (fun n => quenchedPressure (D n) μ (b n)) atTop (𝓝 F) := by
  have hbB : ∀ᶠ n in atTop, b n ≤ β+1 :=
    (hb.eventually (Iio_mem_nhds (by linarith : β < β+1))).mono fun _ h => h.le
  have herr : Tendsto (fun n => quenchedPressure (D n) μ (b n) -
      quenchedPressure (D n) μ β) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      (by
        filter_upwards [hD, hb0, hbB] with n hn hn0 hnB
        simpa only [Real.norm_eq_abs] using
          quenchedPressure_temperature_lipschitz hn μ
            (show b n ∈ Icc 0 (β+1) from ⟨hn0,hnB⟩)
            (show β ∈ Icc 0 (β+1) from ⟨hβ, by linarith⟩))
    simpa using (((hb.sub (tendsto_const_nhds (x := β))).abs).const_mul
      (2*(β+1)*μ.xi 1))
  have hsum := herr.add hfixed
  simpa only [sub_add_cancel, zero_add] using hsum

/-- The actual correction from covariance scale N+j to the standard
N-dimensional spherical covariance. -/
def dimensionCorrectedTemperature (β : ℝ) (j N : ℕ) : ℝ :=
  β * Real.sqrt (((N+j : ℕ) : ℝ)/(N : ℝ))

theorem dimensionCorrectedTemperature_nonneg {β : ℝ} (hβ : 0 ≤ β) (j N : ℕ) :
    0 ≤ dimensionCorrectedTemperature β j N :=
  mul_nonneg hβ (Real.sqrt_nonneg _)

/-- The literal dimension correction converges to its fixed temperature. -/
theorem dimensionCorrectedTemperature_tendsto (β : ℝ) (j : ℕ) :
    Tendsto (dimensionCorrectedTemperature β j) atTop (𝓝 β) := by
  have hratio : Tendsto (fun N : ℕ => ((N+j : ℕ) : ℝ)/(N : ℝ)) atTop (𝓝 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds (j : ℝ) 0 1
      (d := (1 : ℝ)) one_ne_zero
    simpa only [Nat.cast_add,one_mul,zero_add,add_zero,one_div_one,add_comm] using h
  change Tendsto (fun N : ℕ => β*Real.sqrt (((N+j : ℕ) : ℝ)/(N : ℝ))) atTop (𝓝 β)
  simpa only [Real.sqrt_one,mul_one] using hratio.sqrt.const_mul β

/-- Fixed-temperature pressure limits remain valid with the genuine
covariance dimension correction, even at the endpoint of an RS interval. -/
theorem quenchedPressure_tendsto_dimensionCorrectedTemperature (μ : FiniteMixture)
    {β F : ℝ} (hβ : 0 ≤ β) (j : ℕ)
    (hfixed : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 F)) :
    Tendsto (fun N : ℕ => quenchedPressure N μ (dimensionCorrectedTemperature β j N))
      atTop (𝓝 F) := by
  exact quenchedPressure_tendsto_varying_temperature μ id
    (dimensionCorrectedTemperature β j) hβ (eventually_ge_atTop 1)
    (.of_forall (dimensionCorrectedTemperature_nonneg hβ j))
    (dimensionCorrectedTemperature_tendsto β j) hfixed

end
end SlowEquilibration.SphericalModel
