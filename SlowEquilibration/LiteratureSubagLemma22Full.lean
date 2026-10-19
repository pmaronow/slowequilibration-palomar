-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PressureLowerTails
public import SlowEquilibration.SphericalLogPartitionRegularity
public import SlowEquilibration.GaussianMaximalCorrelation
public import SlowEquilibration.SphericalSmoothEhrhard
public import SlowEquilibration.GaussianHermiteLipschitzEnergy
public import SlowEquilibration.SphericalLogPartitionHermiteLowChaos

/-!
A further reduction of the all-temperature part of Subag's Lemma 22.
The literal finite mixtures exclude degrees zero and one, so the source's
no-one-spin assumption is satisfied. The arbitrary-rate pressure lower tail is proved at every real inverse
temperature, without an external literature premise.

The Gaussian Hermite truncation is proved from the complete product Hermite
basis. Fixed-cutoff bounds already imply sublinear log-partition variance:
no growing cutoff or logarithmic optimization is needed. The smooth variance-sensitive lower deviation estimate is proved internally
from the actual spherical log partition. The final assembly uses its true
Gaussian law, its actual mean, and its square integrability. Fixed-order
physical derivative estimates supply the low-chaos bounds and sublinear
variance, proving the exact universal pressure-tail predicate.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagLemma22Full

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel LiteratureSubagBandLowerComplete LiteratureSubagLemma22
open OAI.MinUncut.GaussianHermite GaussianMaximalCorrelation
open scoped Topology BigOperators NNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The spectral truncation underlying Chatterjee's argument. A bound on
the weighted Hermite energy controls all modes above any fixed cutoff.
The function is centered, so the zero mode contributes nothing. -/
theorem gaussian_hermite_truncation {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (hf : MemLp f 2 (γpi ι))
    (hmean : ∫ x, f x ∂γpi ι = 0) {d : ℕ} (hd : 1 ≤ d) {E : ℝ}
    (henergy : ∀ s : Finset (ι → ℕ),
      ∑ a ∈ s, (degree a : ℝ) * (coeff f a) ^ 2 ≤ E) :
    (∫ x, f x ^ 2 ∂γpi ι) ≤
      (∑' a : ι → ℕ, if 0 < degree a ∧ degree a < d then (coeff f a) ^ 2 else 0) +
        E / (d : ℝ) := by
  classical
  let low : (ι → ℕ) → ℝ := fun a =>
    if 0 < degree a ∧ degree a < d then (coeff f a) ^ 2 else 0
  have hlow0 : ∀ a, 0 ≤ low a := by intro a; dsimp [low]; split_ifs <;> positivity
  have hlows : Summable low := (hermite_hasSum_sq hf).summable.of_nonneg_of_le
    hlow0 (fun a => by dsimp [low]; split_ifs; exact le_rfl; exact sq_nonneg _)
  have hdr : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpoint (a : ι → ℕ) :
      (coeff f a) ^ 2 ≤ low a + ((degree a : ℝ) * (coeff f a) ^ 2) / (d : ℝ) := by
    by_cases ha : degree a = 0
    · have ha0 : a = 0 := (degree_eq_zero_iff a).mp ha
      subst a
      simp [coeff_zero, hmean, low, degree]
    · by_cases hsmall : degree a < d
      · rw [show low a = (coeff f a) ^ 2 by simp [low, Nat.pos_of_ne_zero ha, hsmall]]
        exact le_add_of_nonneg_right (by positivity)
      · have hlarge : (d : ℝ) ≤ (degree a : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hsmall)
        have hh := mul_le_mul_of_nonneg_right hlarge (sq_nonneg (coeff f a))
        have hlow : low a = 0 := by simp [low, hsmall]
        rw [hlow, zero_add]
        exact (le_div_iff₀ hdr).mpr (by nlinarith)
  have hpartial (s : Finset (ι → ℕ)) :
      ∑ a ∈ s, (coeff f a) ^ 2 ≤ (∑' a, low a) + E / (d : ℝ) := by
    calc
      _ ≤ ∑ a ∈ s, (low a + ((degree a : ℝ) * (coeff f a) ^ 2) / (d : ℝ)) :=
        Finset.sum_le_sum (fun a _ => hpoint a)
      _ = (∑ a ∈ s, low a) + (∑ a ∈ s, (degree a : ℝ) * (coeff f a) ^ 2) / (d : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ (∑' a, low a) + E / (d : ℝ) :=
        add_le_add (hlows.sum_le_tsum s (fun a _ => hlow0 a))
          (div_le_div_of_nonneg_right (henergy s) hdr.le)
  exact le_of_tendsto (hermite_hasSum_sq hf) (Eventually.of_forall hpartial)

/-- Fixing the chaos cutoff before taking the dimension limit suffices for
superconcentration. The cutoff-dependent constants need no growth bound. -/
theorem sublinear_of_fixed_cutoff_bounds (V A : ℕ → ℝ) (K : ℝ)
    (hV : ∀ N, 0 ≤ V N)
    (hbound : ∀ d : ℕ, 1 ≤ d → ∀ᶠ N : ℕ in atTop,
      V N ≤ A d + K * (N : ℝ) / (d : ℝ)) :
    Tendsto (fun N : ℕ => V N / (N : ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall (fun N =>
      ha.trans_le (div_nonneg (hV N) (Nat.cast_nonneg N)))
  · intro b hb
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / b)
    let d : ℕ := n + 1
    have hd : 1 ≤ d := by dsimp [d]; omega
    have hdr : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
    have hnd : (n : ℝ) ≤ (d : ℝ) := by
      dsimp [d]
      exact_mod_cast Nat.le_succ n
    have hKd : K / (d : ℝ) < b / 2 := by
      have hh := (div_lt_iff₀ hb).mp (hn.trans_le hnd)
      apply (div_lt_iff₀ hdr).mpr
      nlinarith
    have hlim : Tendsto (fun N : ℕ => A d / (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [hbound d hd, hlim.eventually_lt_const (half_pos hb),
      eventually_ge_atTop (1 : ℕ)] with N hB hA hN
    have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    have hh := div_le_div_of_nonneg_right hB hNr.le
    have heq : (A d + K * (N : ℝ) / (d : ℝ)) / (N : ℝ) =
        A d / (N : ℝ) + K / (d : ℝ) := by
      field_simp
    rw [heq] at hh
    linarith

private theorem euclidean_lipschitz_memLp_two {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : LipschitzWith L.toNNReal f) :
    MemLp f 2 (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hid : MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]
    exact IsGaussian.memLp_id _ 2 (by norm_num)
  have hb : MemLp (fun x : EuclideanSpace ℝ ι => L * ‖x‖ + ‖f 0‖) 2
      (SYK.standardGaussianMeasureOnEuclidean ι) :=
    (hid.norm.const_mul L).add (memLp_const _)
  apply hb.mono hf.continuous.aestronglyMeasurable
  filter_upwards [] with x
  have hh := hf.norm_sub_le x 0
  rw [Real.coe_toNNReal L hL, sub_zero] at hh
  have ht := norm_le_norm_sub_add (f x) (f 0)
  rw [Real.norm_of_nonneg (show 0 ≤ L * ‖x‖ + ‖f 0‖ by positivity)]
  linarith

/-- Square integrability of the actual coefficient log partition, at every
real inverse temperature. In particular, its variance is a finite variance. -/
theorem logPartitionEuclidean_memLp_two {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    MemLp (logPartitionEuclidean (N := N) (mixtureCoefficients μ) β) 2
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) :=
  euclidean_lipschitz_memLp_two _ (by positivity)
    (logPartitionEuclidean_lipschitz_all_real hN _ (mixtureCoefficients_nonnegative μ) β)

private theorem variance_euclidean_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    variance (logPartitionEuclidean (N := N) (mixtureCoefficients μ) β)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) =
    variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
      (disorderLaw N μ.maxDegree) := by
  have hlaw := euclideanDisorder_hasLaw N μ.maxDegree
  rw [← hlaw.map_eq]
  exact variance_map (hlaw.map_eq ▸ (logPartitionEuclidean_memLp_two hN μ β).aemeasurable)
    hlaw.aemeasurable

/-- The normalization required by Subag is Var(log Z)/N, equivalently
N times the variance of the pressure. Var(pressure) alone is insufficient. -/
theorem pressure_variance_scaling (N : ℕ) (μ : FiniteMixture) (β : ℝ) :
    (N : ℝ) * variance
      (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J) / (N : ℝ))
      (disorderLaw N μ.maxDegree) =
    variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
      (disorderLaw N μ.maxDegree) / (N : ℝ) := by
  simp only [div_eq_mul_inv, variance_mul_const]
  by_cases hN : N = 0
  · subst N
    simp
  · have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp

/-- A regularized formulation of the still-unproved Paouris--Valettas
analytic input. This definition asserts no theorem. -/
def ConvexGaussianVarianceLowerDeviation (κ : ℝ) : Prop :=
    ∀ (ι : Type) [Fintype ι] (f : EuclideanSpace ℝ ι → ℝ),
      ConvexOn ℝ univ f → (∃ L : ℝ≥0, LipschitzWith L f) →
      MemLp f 2 (SYK.standardGaussianMeasureOnEuclidean ι) →
      ∀ u : ℝ, 0 < u →
        Real.sqrt (variance f (SYK.standardGaussianMeasureOnEuclidean ι) + 1) < u →
        (SYK.standardGaussianMeasureOnEuclidean ι).real
          {x | f x < (∫ y, f y ∂SYK.standardGaussianMeasureOnEuclidean ι) - u} ≤
        Real.exp (-κ * u ^ 2 /
          (variance f (SYK.standardGaussianMeasureOnEuclidean ι) + 1))

/-- The Paouris--Valettas input, with a harmless positive variance
regularization, suffices together with sublinear log-partition variance.
The lower-deviation estimate here is an explicit remaining premise. -/
theorem pressureLowerTails_of_convex_variance_lower_deviation
    (μ : FiniteMixture) (β : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hconvex : ConvexGaussianVarianceLowerDeviation κ)
    (hvariance : Tendsto (fun N : ℕ =>
      variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
        (disorderLaw N μ.maxDegree) / (N : ℝ)) atTop (𝓝 0)) :
    PressureLowerTails μ β := by
  let V : ℕ → ℝ := fun N => variance
    (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
    (disorderLaw N μ.maxDegree)
  have hscale : Tendsto (fun N : ℕ => (V N + 1) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      hvariance.add (show Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  intro t c ht hc
  have hsmall := hscale.eventually_lt_const
    (show 0 < min (κ * t ^ 2 / c) (t ^ 2) by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with N hsmall hN
  let f := logPartitionEuclidean (N := N) (mixtureCoefficients μ) β
  let P := SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hV : 0 ≤ V N := variance_nonneg _ _
  have hvEq : variance f P = V N := variance_euclidean_eq hN μ β
  have hnear : V N + 1 < t ^ 2 * (N : ℝ) :=
    (div_lt_iff₀ hNr).mp (lt_of_lt_of_le hsmall (min_le_right _ _))
  have hcut : Real.sqrt (variance f P + 1) < (N : ℝ) * t := by
    rw [hvEq]
    apply (Real.sqrt_lt (by linarith : 0 ≤ V N + 1) (by positivity)).mpr
    have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg t]
  have hlip := logPartitionEuclidean_lipschitz_all_real hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) β
  have htail := hconvex (Coordinate N μ.maxDegree) f
    (logPartitionEuclidean_convex hN _ (mixtureCoefficients_nonnegative μ) β)
    ⟨_, hlip⟩ (logPartitionEuclidean_memLp_two hN μ β)
    ((N : ℝ) * t) (mul_pos hNr ht) hcut
  have hmean : (∫ J : Disorder N μ.maxDegree, Real.log (mixturePartition μ β J)
      ∂disorderLaw N μ.maxDegree) = ∫ x, f x ∂P :=
    (euclideanDisorder_hasLaw N μ.maxDegree).integral_comp
      hlip.continuous.aestronglyMeasurable
  have hE : MeasurableSet {x | f x < (∫ y, f y ∂P) - (N : ℝ) * t} :=
    measurableSet_lt hlip.continuous.measurable measurable_const
  rw [← (euclideanDisorder_hasLaw N μ.maxDegree).measureReal_eq hE] at htail
  have hset : {J : Disorder N μ.maxDegree |
      Real.log (mixturePartition μ β J) / (N : ℝ) < quenchedPressure N μ β - t} =
      {J | f (euclideanDisorder J) < (∫ y, f y ∂P) - (N : ℝ) * t} := by
    ext J
    change Real.log (mixturePartition μ β J) / (N : ℝ) < quenchedPressure N μ β - t ↔
      Real.log (mixturePartition μ β J) < (∫ y, f y ∂P) - (N : ℝ) * t
    rw [← hmean]
    unfold quenchedPressure
    have heq : (∫ J : Disorder N μ.maxDegree, Real.log (mixturePartition μ β J)
        ∂disorderLaw N μ.maxDegree) / (N : ℝ) - t =
        ((∫ J : Disorder N μ.maxDegree, Real.log (mixturePartition μ β J)
          ∂disorderLaw N μ.maxDegree) - (N : ℝ) * t) / (N : ℝ) := by
      field_simp
    rw [heq, div_lt_iff₀ hNr]
    rw [div_mul_cancel₀ _ hNr.ne']
  rw [hset]
  apply htail.trans
  apply Real.exp_le_exp.mpr
  rw [hvEq]
  have hrate : c * (V N + 1) < κ * t ^ 2 * (N : ℝ) := by
    have hh := (div_lt_iff₀ hNr).mp (lt_of_lt_of_le hsmall (min_le_left _ _))
    rw [div_mul_eq_mul_div] at hh
    have hh' := (lt_div_iff₀ hc).mp hh
    nlinarith
  have hden : 0 < V N + 1 := by linarith
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- A fixed-cutoff variance estimate suffices for the exact all-temperature
tail statement. The constants for different cutoffs can grow arbitrarily. -/
theorem pressureLowerTails_of_fixed_cutoff_variance_bounds
    (μ : FiniteMixture) (β : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hconvex : ConvexGaussianVarianceLowerDeviation κ)
    (A : ℕ → ℝ) (K : ℝ)
    (hbound : ∀ d : ℕ, 1 ≤ d → ∀ᶠ N : ℕ in atTop,
      variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
        (disorderLaw N μ.maxDegree) ≤ A d + K * (N : ℝ) / (d : ℝ)) :
    PressureLowerTails μ β :=
  pressureLowerTails_of_convex_variance_lower_deviation μ β hκ hconvex
    (sublinear_of_fixed_cutoff_bounds _ A K (fun _ => variance_nonneg _ _) hbound)

/-- The centered log partition on the actual independent scalar Gaussian
coordinates, for use with the product Hermite basis. -/
def centeredProductLogPartition (N : ℕ) (μ : FiniteMixture) (β : ℝ)
    (x : Coordinate N μ.maxDegree → ℝ) : ℝ :=
  logPartitionEuclidean (mixtureCoefficients μ) β (WithLp.toLp 2 x) -
    ∫ y, logPartitionEuclidean (mixtureCoefficients μ) β y
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)

private theorem centeredProductLogPartition_data {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    MemLp (centeredProductLogPartition N μ β) 2 (γpi (Coordinate N μ.maxDegree)) ∧
    (∫ x, centeredProductLogPartition N μ β x ∂γpi (Coordinate N μ.maxDegree)) = 0 ∧
    (∫ x, centeredProductLogPartition N μ β x ^ 2 ∂γpi (Coordinate N μ.maxDegree)) =
      variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
        (disorderLaw N μ.maxDegree) := by
  let f := logPartitionEuclidean (N := N) (mixtureCoefficients μ) β
  let P := SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)
  let T : (Coordinate N μ.maxDegree → ℝ) → EuclideanDisorder N μ.maxDegree :=
    WithLp.toLp 2
  have hm : Measurable T :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N μ.maxDegree => ℝ)).symm.continuous.measurable
  have hT : HasLaw T P (γpi (Coordinate N μ.maxDegree)) := hasLaw_map hm.aemeasurable
  have hf : MemLp f 2 P := logPartitionEuclidean_memLp_two hN μ β
  have hcomp : MemLp (fun x => f (T x)) 2 (γpi (Coordinate N μ.maxDegree)) :=
    hT.memLp_fun_comp hf
  have hc : MemLp (centeredProductLogPartition N μ β) 2
      (γpi (Coordinate N μ.maxDegree)) := hcomp.sub (memLp_const _)
  have hmean : (∫ x, f (T x) ∂γpi (Coordinate N μ.maxDegree)) = ∫ y, f y ∂P :=
    hT.integral_comp hf.aestronglyMeasurable
  refine ⟨hc, ?_, ?_⟩
  · change (∫ x, f (T x) - ∫ y, f y ∂P ∂γpi (Coordinate N μ.maxDegree)) = 0
    rw [integral_sub (hcomp.integrable (by norm_num)) (integrable_const _),
      integral_const, hmean]
    simp
  · calc
      _ = ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P :=
        hT.integral_comp ((hf.sub (memLp_const _)).aestronglyMeasurable.pow 2)
      _ = variance f P := (variance_eq_integral hf.aemeasurable).symm
      _ = _ := variance_euclidean_eq hN μ β

/-- The physical Gaussian gradient bound supplies the entire weighted
Hermite energy, including every tensor coordinate without a dimension loss. -/
theorem centeredProductLogPartition_weighted_energy {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (s : Finset (Coordinate N μ.maxDegree → ℕ)) :
    ∑ a ∈ s, (degree a : ℝ) *
      (coeff (centeredProductLogPartition N μ β) a)^2 ≤
        (β^2 * μ.xi 1) * (N : ℝ) := by
  classical
  let f : EuclideanDisorder N μ.maxDegree → ℝ := fun x =>
    logPartitionEuclidean (mixtureCoefficients μ) β x -
      ∫ y, logPartitionEuclidean (mixtureCoefficients μ) β y
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)
  let L : ℝ≥0 := (|β| * Real.sqrt
    ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1)).toNNReal
  have hf : ContDiff ℝ 1 f :=
    ((logPartitionEuclidean_contDiff_two hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β).of_le (by norm_num)).sub contDiff_const
  have hlip : LipschitzWith L f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [f, Real.dist_eq, sub_sub_sub_cancel_right] using
      (logPartitionEuclidean_lipschitz_all_real hN (mixtureCoefficients μ)
        (mixtureCoefficients_nonnegative μ) β).dist_le_mul x y
  have hf2 : MemLp (fun x : Coordinate N μ.maxDegree → ℝ => f (WithLp.toLp 2 x))
      2 (γpi (Coordinate N μ.maxDegree)) :=
    (centeredProductLogPartition_data hN μ β).1
  have he := GaussianHermiteDerivative.finite_weighted_energy_le_lipschitz_square
    f hf L hlip hf2 s
  have hxi : 0 ≤ covariancePolynomial (mixtureCoefficients μ) 1 := by
    rw [covariancePolynomial_mixture]
    exact (μ.xi_pos zero_lt_one).le
  have hLeq : (L : ℝ)^2 = (β^2 * μ.xi 1) * (N : ℝ) := by
    dsimp only [L]
    rw [Real.coe_toNNReal _ (mul_nonneg (abs_nonneg β) (Real.sqrt_nonneg _)),
      mul_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hxi), sq_abs,
      covariancePolynomial_mixture]
    ring
  change (∑ a ∈ s, (degree a : ℝ) *
    (coeff (centeredProductLogPartition N μ β) a)^2) ≤ (L : ℝ)^2 at he
  rwa [hLeq] at he

/-- Fixed low-chaos bounds imply sublinear physical log-partition variance;
the weighted-energy estimate is supplied by the actual spin features. -/
theorem logPartition_variance_sublinear_of_low_chaos_bounds
    (μ : FiniteMixture) (β : ℝ) (A : ℕ → ℝ)
    (hlow : ∀ d : ℕ, 1 ≤ d → ∀ᶠ N : ℕ in atTop,
      (∑' a : Coordinate N μ.maxDegree → ℕ,
        if 0 < degree a ∧ degree a < d then
          (coeff (centeredProductLogPartition N μ β) a)^2 else 0) ≤ A d) :
    Tendsto (fun N : ℕ =>
      variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
        (disorderLaw N μ.maxDegree) / (N : ℝ)) atTop (𝓝 0) := by
  apply sublinear_of_fixed_cutoff_bounds _ A (β^2 * μ.xi 1)
    (fun N => variance_nonneg _ _)
  intro d hd
  filter_upwards [hlow d hd, eventually_ge_atTop (1 : ℕ)] with N hlow hN
  obtain ⟨hf, hmean, hvariance⟩ := centeredProductLogPartition_data hN μ β
  have htrunc := gaussian_hermite_truncation (centeredProductLogPartition N μ β)
    hf hmean hd (centeredProductLogPartition_weighted_energy hN μ β)
  rw [hvariance] at htrunc
  exact htrunc.trans (add_le_add hlow le_rfl)

/-- The full fixed-chaos reduction for the literal tensor disorder. The
remaining physical estimates are the weighted Hermite energy bound and a
dimension-independent bound on each fixed low-chaos sum. Together with the
convex Gaussian analytic inequality they imply exactly Lemma 22, at any β. -/
theorem pressureLowerTails_of_hermite_bounds
    (μ : FiniteMixture) (β : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hconvex : ConvexGaussianVarianceLowerDeviation κ)
    (A : ℕ → ℝ) (K : ℝ)
    (henergy : ∀ N : ℕ, 1 ≤ N → ∀ s : Finset (Coordinate N μ.maxDegree → ℕ),
      ∑ a ∈ s, (degree a : ℝ) * (coeff (centeredProductLogPartition N μ β) a) ^ 2 ≤
        K * (N : ℝ))
    (hlow : ∀ d : ℕ, 1 ≤ d → ∀ᶠ N : ℕ in atTop,
      (∑' a : Coordinate N μ.maxDegree → ℕ,
        if 0 < degree a ∧ degree a < d then
          (coeff (centeredProductLogPartition N μ β) a) ^ 2 else 0) ≤ A d) :
    PressureLowerTails μ β := by
  apply pressureLowerTails_of_fixed_cutoff_variance_bounds μ β hκ hconvex A K
  intro d hd
  filter_upwards [hlow d hd, eventually_ge_atTop (1 : ℕ)] with N hlow hN
  obtain ⟨hf, hmean, hvariance⟩ := centeredProductLogPartition_data hN μ β
  have htrunc := gaussian_hermite_truncation (centeredProductLogPartition N μ β)
    hf hmean hd (henergy N hN)
  rw [hvariance] at htrunc
  exact htrunc.trans (add_le_add hlow le_rfl)

/-- The specialized smooth lower-tail estimate with cutoff `8 * sqrt (V+1)`
is sufficient for the exact pressure-tail predicate. This assembly does not
require the stronger generic convex-tail interface above. Both analytic
inputs remain explicit hypotheses until their physical proofs are supplied. -/
theorem pressureLowerTails_of_logPartition_lower_deviation
    (μ : FiniteMixture) (β : ℝ)
    (hvariance : Tendsto (fun N : ℕ =>
      variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
        (disorderLaw N μ.maxDegree) / (N : ℝ)) atTop (𝓝 0))
    (htail : ∀ N : ℕ, 1 ≤ N → ∀ u : ℝ,
      8 * Real.sqrt (variance
        (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
        (disorderLaw N μ.maxDegree) + 1) ≤ u →
      (disorderLaw N μ.maxDegree).real
        {J | Real.log (mixturePartition μ β J) <
          (∫ D : Disorder N μ.maxDegree, Real.log (mixturePartition μ β D)
            ∂disorderLaw N μ.maxDegree) - u} ≤
        Real.exp (-u ^ 2 / (64 * (variance
          (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
          (disorderLaw N μ.maxDegree) + 1)))) :
    PressureLowerTails μ β := by
  let V : ℕ → ℝ := fun N => variance
    (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
    (disorderLaw N μ.maxDegree)
  have hscale : Tendsto (fun N : ℕ => (V N + 1) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      hvariance.add (show Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  intro t c ht hc
  have hsmall := hscale.eventually_lt_const
    (show 0 < t ^ 2 / (64 * (c + 1)) by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with N hsmall hN
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hV : 0 ≤ V N := variance_nonneg _ _
  have hden : 0 < V N + 1 := by linarith
  have hrate : 64 * (c + 1) * (V N + 1) < t ^ 2 * (N : ℝ) := by
    have hh := (div_lt_div_iff₀ hNr
      (show 0 < 64 * (c + 1) by positivity)).mp hsmall
    nlinarith
  have hcut : 8 * Real.sqrt (V N + 1) ≤ (N : ℝ) * t := by
    have hs := Real.sq_sqrt hden.le
    have hs0 := Real.sqrt_nonneg (V N + 1)
    have h64 : 64 * (V N + 1) < t ^ 2 * (N : ℝ) := by
      nlinarith [mul_nonneg hc.le hden.le]
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hN2 (sq_nonneg t)
    apply (sq_le_sq₀ (by positivity : 0 ≤ 8*Real.sqrt (V N+1))
      (by positivity : 0 ≤ (N : ℝ)*t)).mp
    nlinarith only [hs, h64, hmul]
  have htailN := htail N hN ((N : ℝ) * t) hcut
  have hset : {J : Disorder N μ.maxDegree |
      Real.log (mixturePartition μ β J) / (N : ℝ) < quenchedPressure N μ β - t} =
      {J | Real.log (mixturePartition μ β J) <
        (∫ D : Disorder N μ.maxDegree, Real.log (mixturePartition μ β D)
          ∂disorderLaw N μ.maxDegree) - (N : ℝ) * t} := by
    ext J
    unfold quenchedPressure
    rw [show (∫ D : Disorder N μ.maxDegree, Real.log (mixturePartition μ β D)
        ∂disorderLaw N μ.maxDegree) / (N : ℝ) - t =
        ((∫ D : Disorder N μ.maxDegree, Real.log (mixturePartition μ β D)
          ∂disorderLaw N μ.maxDegree) - (N : ℝ) * t) / (N : ℝ) by field_simp]
    exact (div_lt_div_iff_of_pos_right hNr)
  rw [hset]
  apply htailN.trans
  apply Real.exp_le_exp.mpr
  change -((N : ℝ) * t) ^ 2 / (64 * (V N + 1)) ≤ -c * (N : ℝ)
  apply (div_le_iff₀ (show 0 < 64 * (V N + 1) by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right hrate.le hNr.le
  nlinarith [mul_nonneg hNr.le hden.le]

/-- The smooth lower deviation estimate is internal. Sublinear variance of
the actual logarithmic partition is sufficient for all pressure lower tails,
at any real temperature and with the actual finite-dimensional mean. -/
theorem pressureLowerTails_of_sublinear_variance
    (μ : FiniteMixture) (β : ℝ)
    (hvariance : Tendsto (fun N : ℕ =>
      variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
        (disorderLaw N μ.maxDegree) / (N : ℝ)) atTop (𝓝 0)) :
    PressureLowerTails μ β := by
  apply pressureLowerTails_of_logPartition_lower_deviation μ β hvariance
  intro N hN u hu
  let f := logPartitionEuclidean (N := N) (mixtureCoefficients μ) β
  let P := SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)
  have hvEq : variance f P = variance
      (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
      (disorderLaw N μ.maxDegree) := variance_euclidean_eq hN μ β
  have hcut : 8*Real.sqrt (variance f P+1) ≤ u := by rwa [hvEq]
  have htail := logPartitionEuclidean_gaussian_lower_tail hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) β hcut
  have htail' : P.real {x | f x ≤ (∫ y, f y ∂P)-u} ≤
      Real.exp (-u^2/(64*(variance f P+1))) := htail
  have hsub : {x | f x < (∫ y, f y ∂P)-u} ⊆
      {x | f x ≤ (∫ y, f y ∂P)-u} := by
    intro x hx
    change f x < (∫ y, f y ∂P)-u at hx
    change f x ≤ (∫ y, f y ∂P)-u
    exact hx.le
  have hstrict := (measureReal_mono (μ := P) hsub).trans htail'
  have hf := logPartitionEuclidean_memLp_two hN μ β
  have hmean : (∫ J : Disorder N μ.maxDegree, Real.log (mixturePartition μ β J)
      ∂disorderLaw N μ.maxDegree) = ∫ x, f x ∂P :=
    (euclideanDisorder_hasLaw N μ.maxDegree).integral_comp hf.aestronglyMeasurable
  have hE : MeasurableSet {x | f x < (∫ y, f y ∂P)-u} :=
    measurableSet_lt (logPartitionEuclidean_contDiff_two hN (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) β).continuous.measurable measurable_const
  rw [← (euclideanDisorder_hasLaw N μ.maxDegree).measureReal_eq hE] at hstrict
  change (disorderLaw N μ.maxDegree).real
    {J | Real.log (mixturePartition μ β J) < (∫ y, f y ∂P)-u} ≤ _ at hstrict
  rw [← hmean, hvEq] at hstrict
  exact hstrict

/-- Sublinear variance of the actual finite-mixture log partition at every
real inverse temperature. -/
theorem logPartition_variance_sublinear (μ : FiniteMixture) (β : ℝ) :
    Tendsto (fun N : ℕ =>
      variance (fun J : Disorder N μ.maxDegree => Real.log (mixturePartition μ β J))
        (disorderLaw N μ.maxDegree) / (N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := SphericalLogPartitionHermiteLowChaos.low_chaos_eventually_bounded μ β
  apply logPartition_variance_sublinear_of_low_chaos_bounds μ β A
  intro d hd
  filter_upwards [hA d hd] with N hN
  have hf : centeredProductLogPartition N μ β =
      (fun x : Coordinate N μ.maxDegree → ℝ =>
        logPartitionEuclidean (mixtureCoefficients μ) β (WithLp.toLp 2 x) -
          ∫ y, logPartitionEuclidean (mixtureCoefficients μ) β y
            ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) := by
    funext x
    rfl
  rw [hf]
  exact hN (∫ y, logPartitionEuclidean (mixtureCoefficients μ) β y
    ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree))

/-- Universal arbitrary-rate lower tails of the actual finite-mixture
pressure, with its finite-dimensional mean and every real temperature. -/
theorem pressureLowerTails (μ : FiniteMixture) (β : ℝ) : PressureLowerTails μ β :=
  pressureLowerTails_of_sublinear_variance μ β (logPartition_variance_sublinear μ β)

theorem universalPressureLowerTails : ∀ μ : FiniteMixture, ∀ β : ℝ,
    LiteratureSubagBandLowerComplete.PressureLowerTails μ β :=
  pressureLowerTails

end SlowEquilibration.LiteratureSubagLemma22Full
