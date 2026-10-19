-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagProposition24
public import SlowEquilibration.SphericalGaussianInterpolation
public import SlowEquilibration.SourceMixedBandsLiteral
public import SlowEquilibration.SourcePureCaptureReplicaNetGeometry
public import SlowEquilibration.SourceMixedCountCapturePackage
public import SlowEquilibration.SphericalSpatialRegularity
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Subag's replicated-band concentration for the physical finite-mixture model

This proves the exact `LiteratureSubagProposition24.Proposition24` interface
from Section 3, equation (3.1), of Subag, arXiv:1804.10576v6. The proof
computes the actual replicated-field covariance, applies Gaussian concentration
to the literal restricted partition, proves arbitrary-rate ball Lipschitz
tails, transports centers by two reflections, and takes a finite-net union
bound. The strict uniform event and the original parameter order are retained.
No Parisi formula or other literature interface is assumed.

The two principal downstream endpoints are restated without the Proposition 24
hypothesis. Their other original literature hypotheses are unchanged.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Set
open SphericalModel LiteratureSubagPhysicalDefinitions
open scoped BigOperators
set_option autoImplicit false

/-- Nonnegative coefficients bound the absolute derivative throughout the
entire overlap interval, including the negative overlaps of odd models. -/
private theorem xi1_abs_le_at_one (μ : FiniteMixture) {r : ℝ} (hr : |r| ≤ 1) :
    |μ.xi1 r| ≤ μ.xi1 1 := by
  unfold FiniteMixture.xi1
  calc
    |∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ) * r ^ (p - 1)| ≤
        ∑ p ∈ μ.coeff.support, |μ.coeff p * (p : ℝ) * r ^ (p - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ) * 1 ^ (p - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p)),
        abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg r) hr _)
        (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))

/-- The covariance is Lipschitz with the source constant `ν'(1)` on
`[-1,1]`, without any parity assumption on the mixture. -/
private theorem xi_sub_abs_le (μ : FiniteMixture) {r s : ℝ}
    (hr : |r| ≤ 1) (hs : |s| ≤ 1) :
    |μ.xi r - μ.xi s| ≤ μ.xi1 1 * |r - s| := by
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (μ.hasDerivAt_xi x).differentiableAt)
    (fun x hx => by
      rw [(μ.hasDerivAt_xi x).deriv, Real.norm_eq_abs]
      exact xi1_abs_le_at_one μ (abs_le.mpr hx))
    (abs_le.mp hs) (abs_le.mp hr)
  simpa only [Real.norm_eq_abs] using h

/-- The physical Hamiltonian summed over the replicas, with the center
field removed once for each replica, as in the exponent of (1.10). -/
def replicatedField {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (m : Vector N) (σ : Fin k → Vector N) (J : Disorder N μ.maxDegree) : ℝ :=
  ∑ i : Fin k, (field (mixtureCoefficients μ) J (σ i) -
    field (mixtureCoefficients μ) J m)

/-- The physical replicated field has a finite second moment at every
fixed configuration; no residual-field replacement is involved. -/
private theorem replicatedField_memLp {N k : ℕ} (μ : FiniteMixture)
    (m : Vector N) (σ : Fin k → Vector N) :
    MemLp (replicatedField k μ m σ) 2 (disorderLaw N μ.maxDegree) := by
  exact memLp_finsetSum _ (fun i _ =>
    (field_memLp (mixtureCoefficients μ) (σ i)).sub
      (field_memLp (mixtureCoefficients μ) m))

/-- Exact covariance expansion of the actual replicated field under the
original disorder law. This is the quantity `NV` in Subag's proof. -/
private theorem replicatedField_variance_eq {N k : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (q : ℝ) (m : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q) (σ : Fin k → Vector N) :
    variance (replicatedField k μ m σ) (disorderLaw N μ.maxDegree) =
      (N : ℝ) * ∑ i : Fin k, ∑ j : Fin k,
        (μ.xi (overlap (σ i) (σ j)) - μ.xi (overlap (σ i) m) -
          μ.xi (overlap (σ j) m) + μ.xi q) := by
  have hmm : overlap m m = q := by
    rw [overlap, real_inner_self_eq_norm_sq, hm]
    exact mul_div_cancel_left₀ q (Nat.cast_ne_zero.mpr hN.ne')
  have hmem (i : Fin k) : MemLp (fun J : Disorder N μ.maxDegree =>
      field (mixtureCoefficients μ) J (σ i) -
        field (mixtureCoefficients μ) J m) 2 (disorderLaw N μ.maxDegree) :=
    (field_memLp (mixtureCoefficients μ) (σ i)).sub
      (field_memLp (mixtureCoefficients μ) m)
  rw [← covariance_self (replicatedField_memLp μ m σ).aemeasurable]
  change covariance (fun J : Disorder N μ.maxDegree => ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m))
    (fun J => ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m))
    (disorderLaw N μ.maxDegree) = _
  rw [covariance_fun_sum_fun_sum hmem hmem, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [covariance_fun_sub_fun_sub
    (field_memLp (mixtureCoefficients μ) (σ i))
    (field_memLp (mixtureCoefficients μ) m)
    (field_memLp (mixtureCoefficients μ) (σ j))
    (field_memLp (mixtureCoefficients μ) m)]
  simp_rw [field_covariance hN _ (mixtureCoefficients_nonnegative μ),
    covariancePolynomial_mixture]
  rw [hmm]
  have hsym : overlap m (σ j) = overlap (σ j) m := by
    simp only [overlap, real_inner_comm]
  rw [hsym]
  ring

private theorem overlap_abs_le_one_of_norm_sq_le {N : ℕ} (hN : 0 < N)
    (x y : Vector N) (hx : ‖x‖ ^ 2 ≤ (N : ℝ))
    (hy : ‖y‖ ^ 2 ≤ (N : ℝ)) : |overlap x y| ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [overlap, abs_div, abs_of_pos hNr]
  apply (div_le_one hNr).mpr
  calc
    |inner ℝ x y| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
    _ ≤ (N : ℝ) := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem xi_nonneg (μ : FiniteMixture) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ μ.xi q := by
  unfold FiniteMixture.xi
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (μ.nonneg p) (pow_nonneg hq p))

private theorem xi1_one_nonneg (μ : FiniteMixture) : 0 ≤ μ.xi1 1 := by
  unfold FiniteMixture.xi1
  exact Finset.sum_nonneg (fun p _ =>
    mul_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p)) (by positivity))

/-- Subag's uniform variance proxy, derived for the repository's physical
replicated band and original tensor law. The diagonal contributes only
`k ξ(1)`; the other contribution vanishes with the band tolerances. -/
theorem replicatedField_variance_le {N k : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q δ ρ : ℝ} (hq : q ∈ Ico (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (m : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q) (σ : Fin k → Vector N)
    (hσ : ∀ i, ‖σ i‖ ^ 2 = (N : ℝ))
    (hband : σ ∈ ReplicatedBand k q δ ρ m) :
    variance (replicatedField k μ m σ) (disorderLaw N μ.maxDegree) ≤
      (N : ℝ) * ((k : ℝ) * μ.xi 1 +
        μ.xi1 1 * (k : ℝ) ^ 2 * (ρ + 2 * δ)) := by
  have hD := xi1_one_nonneg μ
  have hqabs : |q| ≤ 1 := by rw [abs_of_nonneg hq.1]; exact hq.2.le
  have hmle : ‖m‖ ^ 2 ≤ (N : ℝ) := by
    rw [hm]
    exact mul_le_of_le_one_right (Nat.cast_nonneg N) hq.2.le
  have hRm (i : Fin k) : |overlap (σ i) m| ≤ 1 :=
    overlap_abs_le_one_of_norm_sq_le hN _ _ (hσ i).le hmle
  have hR (i j : Fin k) : |overlap (σ i) (σ j)| ≤ 1 :=
    overlap_abs_le_one_of_norm_sq_le hN _ _ (hσ i).le (hσ j).le
  have hcenter (i : Fin k) :
      |μ.xi (overlap (σ i) m) - μ.xi q| ≤ μ.xi1 1 * δ := by
    calc
      _ ≤ μ.xi1 1 * |overlap (σ i) m - q| := xi_sub_abs_le μ (hRm i) hqabs
      _ ≤ μ.xi1 1 * δ := by
        apply mul_le_mul_of_nonneg_left _ hD
        exact (hband.1 i).trans
          (mul_le_of_le_one_right hδ (Real.sqrt_le_one.mpr hq.2.le))
  have hpair (i j : Fin k) :
      μ.xi (overlap (σ i) (σ j)) - μ.xi (overlap (σ i) m) -
          μ.xi (overlap (σ j) m) + μ.xi q ≤
        (if i = j then μ.xi 1 else 0) + μ.xi1 1 * (ρ + 2 * δ) := by
    have hi := neg_le_abs (μ.xi (overlap (σ i) m) - μ.xi q)
    have hj := neg_le_abs (μ.xi (overlap (σ j) m) - μ.xi q)
    have hci := hcenter i
    have hcj := hcenter j
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, overlap_self hN _ (hσ i)]
      have hnonneg := xi_nonneg μ hq.1
      have hDρ := mul_nonneg hD hρ
      linarith
    · rw [ite_eq_right hij]
      have hij' : μ.xi (overlap (σ i) (σ j)) - μ.xi q ≤ μ.xi1 1 * ρ := by
        calc
          _ ≤ |μ.xi (overlap (σ i) (σ j)) - μ.xi q| := le_abs_self _
          _ ≤ μ.xi1 1 * |overlap (σ i) (σ j) - q| :=
            xi_sub_abs_le μ (hR i j) hqabs
          _ ≤ μ.xi1 1 * ρ :=
            mul_le_mul_of_nonneg_left (hband.2 i j hij).le hD
      linarith
  rw [replicatedField_variance_eq hN μ q m hm σ]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  calc
    _ ≤ ∑ i : Fin k, ∑ j : Fin k,
        ((if i = j then μ.xi 1 else 0) + μ.xi1 1 * (ρ + 2 * δ)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The genuine coefficient feature of the replicated Hamiltonian. -/
private def replicatedFeature {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (m : Vector N) (σ : Fin k → Vector N) : EuclideanDisorder N μ.maxDegree :=
  ∑ i : Fin k, (fieldFeature (mixtureCoefficients μ) (σ i) -
    fieldFeature (mixtureCoefficients μ) m)

/-- The feature represents the literal physical replicated Hamiltonian. -/
private theorem replicatedField_eq_inner {N k : ℕ} (μ : FiniteMixture)
    (m : Vector N) (σ : Fin k → Vector N) (g : EuclideanDisorder N μ.maxDegree) :
    replicatedField k μ m σ (unpackDisorder g) = inner ℝ g (replicatedFeature k μ m σ) := by
  simp only [replicatedField, replicatedFeature, inner_sum, inner_sub_right,
    fieldFeature_inner]

/-- The squared coefficient norm is exactly the variance of the physical
replicated field under the original disorder law. -/
private theorem replicatedFeature_norm_sq_eq_variance {N k : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) (m : Vector N) (σ : Fin k → Vector N) :
    ‖replicatedFeature k μ m σ‖ ^ 2 =
      variance (replicatedField k μ m σ) (disorderLaw N μ.maxDegree) := by
  have hmem (i : Fin k) : MemLp (fun J : Disorder N μ.maxDegree =>
      field (mixtureCoefficients μ) J (σ i) -
        field (mixtureCoefficients μ) J m) 2 (disorderLaw N μ.maxDegree) :=
    (field_memLp (mixtureCoefficients μ) (σ i)).sub
      (field_memLp (mixtureCoefficients μ) m)
  rw [← covariance_self (replicatedField_memLp μ m σ).aemeasurable]
  change ‖∑ i : Fin k, (fieldFeature (mixtureCoefficients μ) (σ i) -
      fieldFeature (mixtureCoefficients μ) m)‖ ^ 2 =
    covariance (fun J : Disorder N μ.maxDegree => ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m))
      (fun J => ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m))
      (disorderLaw N μ.maxDegree)
  rw [covariance_fun_sum_fun_sum hmem hmem, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, inner_sub_left, inner_sub_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [covariance_fun_sub_fun_sub
    (field_memLp (mixtureCoefficients μ) (σ i))
    (field_memLp (mixtureCoefficients μ) m)
    (field_memLp (mixtureCoefficients μ) (σ j))
    (field_memLp (mixtureCoefficients μ) m)]
  simp_rw [fieldFeature_inner_gram (show 1 ≤ N by omega) _
    (mixtureCoefficients_nonnegative μ),
    field_covariance hN _ (mixtureCoefficients_nonnegative μ)]
  ring

/-- The variance proxy also bounds the true coefficient feature used by
Gaussian concentration of the replicated log partition. -/
private theorem replicatedFeature_norm_sq_le {N k : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {q δ ρ : ℝ} (hq : q ∈ Ico (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (m : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q) (σ : Fin k → Vector N)
    (hσ : ∀ i, ‖σ i‖ ^ 2 = (N : ℝ))
    (hband : σ ∈ ReplicatedBand k q δ ρ m) :
    ‖replicatedFeature k μ m σ‖ ^ 2 ≤
      (N : ℝ) * ((k : ℝ) * μ.xi 1 +
        μ.xi1 1 * (k : ℝ) ^ 2 * (ρ + 2 * δ)) := by
  rw [replicatedFeature_norm_sq_eq_variance hN]
  exact replicatedField_variance_le hN μ hq hδ hρ m hm σ hσ hband

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof
open MeasureTheory ProbabilityTheory Set SphericalModel
open SourceMixedBandsLiteral.BallLipschitz
open SphericalAging.GaussianLandscape
open scoped BigOperators
set_option autoImplicit false

private theorem actualBallLipschitz_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (physicalBallLipschitzConstant (N := N) c) := by
  unfold physicalBallLipschitzConstant
  apply (isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).continuous_sSup
  exact (PairConditionalDeterminantMoments.source_param_fderiv_contDiff
    (fun J x => field c J x)
    (PairConditionalDeterminantMoments.source_field_joint_contDiff c)).continuous.norm

private theorem actualBallLipschitz_le_envelope {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) (J : Disorder N P) :
    physicalBallLipschitzConstant c J ≤
      normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ) := by
  unfold physicalBallLipschitzConstant
  apply csSup_le
  · exact ⟨‖fderiv ℝ (field c J) 0‖, 0,
      by simpa only [Metric.mem_closedBall, dist_self] using Real.sqrt_nonneg (N : ℝ), rfl⟩
  · rintro v ⟨x, hx, rfl⟩
    have hball : ‖x‖ ≤ Real.sqrt (N : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hjet := field_iteratedFDeriv_ball_bound
      hN c J x hball 1
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
    have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    simp only [pow_one, norm_iteratedFDeriv_one, Nat.descFactorial_one] at hjet
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ (N : ℝ) * normalizedLipschitzEnvelope c J := hjet
      _ = Real.sqrt (N : ℝ) *
          (normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ)) := by
        calc
          _ = normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ) ^ 2 := by rw [hsq]; ring
          _ = _ := by ring

/-- Lemma 17 with any prescribed exponential rate, for the actual maximum
of the field derivative on the physical ball. The degreewise tensor-net
tails allow the threshold to be chosen before the dimension. -/
private theorem physicalBallLipschitz_arbitrary_rate (μ : FiniteMixture)
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      MeasurableSet {J : Disorder N μ.maxDegree |
        C * Real.sqrt (N : ℝ) <
          physicalBallLipschitzConstant (mixtureCoefficients μ) J} ∧
      (disorderLaw N μ.maxDegree).real
        {J | C * Real.sqrt (N : ℝ) <
          physicalBallLipschitzConstant (mixtureCoefficients μ) J} ≤
        Real.exp (-a * (N : ℝ)) := by
  classical
  let d : ℝ := Fintype.card (Degree μ.maxDegree)
  let r : ℝ := a + d + 2
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hr : 1 ≤ r := by dsimp [r]; linarith
  let threshold (p : Degree μ.maxDegree) : ℝ :=
    landscapeThreshold p.val.val + 4 * r
  have hthreshold (p : Degree μ.maxDegree) :
      landscapeThreshold p.val.val ≤ threshold p := by
    dsimp [threshold]; linarith
  have hthresholdpos (p : Degree μ.maxDegree) : 0 < threshold p :=
    (landscapeThreshold_pos _).trans_le (hthreshold p)
  have hthresholdsq (p : Degree μ.maxDegree) : 16 * r ≤ (threshold p) ^ 2 := by
    have hnonneg := (landscapeThreshold_pos p.val.val).le
    have hrr : r ≤ r ^ 2 := by nlinarith
    dsimp [threshold]
    nlinarith [sq_nonneg (landscapeThreshold p.val.val)]
  let C : ℝ := 1 + ∑ p : Degree μ.maxDegree,
    Real.sqrt (mixtureCoefficients μ p) * (p.val.val : ℝ) * threshold p
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ p : Degree μ.maxDegree,
        Real.sqrt (mixtureCoefficients μ p) * (p.val.val : ℝ) * threshold p :=
      Finset.sum_nonneg fun p _ => by
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          (hthresholdpos p).le
    dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N hN
  refine ⟨measurableSet_lt measurable_const
    (actualBallLipschitz_continuous _).measurable, ?_⟩
  let E (p : Degree μ.maxDegree) : Set (Disorder N μ.maxDegree) :=
    {J | threshold p < landscapeNorm N p.val.val (J p)}
  have hsubset : {J : Disorder N μ.maxDegree |
      C * Real.sqrt (N : ℝ) < physicalBallLipschitzConstant (mixtureCoefficients μ) J}
      ⊆ ⋃ p : Degree μ.maxDegree, E p := by
    intro J hJ
    by_contra hn
    have hbound (p : Degree μ.maxDegree) :
        landscapeNorm N p.val.val (J p) ≤ threshold p := by
      by_contra hp
      exact hn (mem_iUnion.mpr ⟨p, not_le.mp hp⟩)
    have henvelope : normalizedLipschitzEnvelope (mixtureCoefficients μ) J ≤ C := by
      unfold normalizedLipschitzEnvelope
      apply le_trans (Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (hbound p)
          (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)))
      dsimp [C]; linarith
    have hLip := actualBallLipschitz_le_envelope (by omega : 1 ≤ N)
      (mixtureCoefficients μ) J
    have hmul := mul_le_mul_of_nonneg_right henvelope (Real.sqrt_nonneg (N : ℝ))
    exact (not_lt_of_ge (hLip.trans hmul)) hJ
  have htail (p : Degree μ.maxDegree) :
      (disorderLaw N μ.maxDegree).real (E p) ≤
        2 * Real.exp (-(N : ℝ) * r) := by
    have hmeas : MeasurableSet {J : SphericalAging.FiniteModel.Disorder N p.val.val |
        threshold p < landscapeNorm N p.val.val J} :=
      measurableSet_lt measurable_const (landscapeNorm_continuous _ _).measurable
    have hlaw := (degree_block_hasLaw (N := N) p).measureReal_eq hmeas
    change (disorderLaw N μ.maxDegree).real
      {J | threshold p < landscapeNorm N p.val.val (J p)} ≤ _
    rw [hlaw]
    apply (landscape_tail_dimension (by omega : 0 < N)
      (by have hp := p.property; omega : 0 < p.val.val) (hthreshold p)).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have hh := mul_le_mul_of_nonneg_left (hthresholdsq p) (Nat.cast_nonneg N)
    nlinarith
  have hsum : (disorderLaw N μ.maxDegree).real
      (⋃ p : Degree μ.maxDegree, E p) ≤
        2 * d * Real.exp (-(N : ℝ) * r) := by
    calc
      _ ≤ ∑ p : Degree μ.maxDegree, (disorderLaw N μ.maxDegree).real (E p) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : Degree μ.maxDegree, 2 * Real.exp (-(N : ℝ) * r) :=
        Finset.sum_le_sum fun p _ => htail p
      _ = _ := by simp [d]; ring
  have hcoef : 2 * d ≤ Real.exp (d + 1) := by
    have hde : d ≤ Real.exp d := by linarith [Real.add_one_le_exp d]
    calc
      _ ≤ 2 * Real.exp d := mul_le_mul_of_nonneg_left hde (by norm_num)
      _ ≤ Real.exp 1 * Real.exp d :=
        mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (measureReal_mono hsubset).trans (hsum.trans ?_)
  calc
    _ ≤ Real.exp (d + 1) * Real.exp (-(N : ℝ) * r) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = Real.exp (d + 1 - (N : ℝ) * r) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-a * (N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hh := mul_le_mul_of_nonneg_left hNr (show 0 ≤ d + 2 by linarith)
      dsimp [r]
      nlinarith

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagProposition24
open scoped BigOperators
set_option autoImplicit false

/-- Continuity of the physical replicated pressure in the original disorder,
with the center and band parameters fixed. -/
private def FixedCenterContinuity (μ : FiniteMixture) (β q : ℝ) : Prop :=
  ∀ N k : ℕ, ∀ δ ρ : ℝ, ∀ m : Vector N,
    Continuous (fun J : Disorder N μ.maxDegree =>
      replicatedBandPressure k μ β q δ ρ J m)

/-- The fixed-center Gaussian step of Proposition 24: making the covariance
proxy small gives any prescribed exponential rate before taking dimension. -/
private def FixedCenterConcentration (μ : FiniteMixture) (β q : ℝ) : Prop :=
  ∀ t c : ℝ, 0 < t → 0 < c →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ k₀ : ℕ,
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∀ k : ℕ, k₀ ≤ k → ∀ N : ℕ, k + 1 ≤ N →
      ∀ m : Vector N, ‖m‖ ^ 2 = (N : ℝ) * q →
        (disorderLaw N μ.maxDegree).real
          {J | t < |replicatedBandPressure k μ β q δ ρ J m -
            expectedReplicatedBandPressure k μ β q δ ρ m|} ≤
          Real.exp (-c * (N : ℝ))

/-- The rotation/Lemma 17 step: outside an event with any prescribed
exponential rate, center variation has a dimension-normalized modulus. -/
private def CenterLipschitzControl (μ : FiniteMixture) (β q : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ L : ℝ, 0 < L ∧
    ∀ N : ℕ, 2 ≤ N → ∃ Ω : Set (Disorder N μ.maxDegree),
      MeasurableSet Ω ∧
      (disorderLaw N μ.maxDegree).real Ωᶜ ≤ Real.exp (-c * (N : ℝ)) ∧
      ∀ J ∈ Ω, ∀ k : ℕ, ∀ δ ρ : ℝ,
      ∀ m m' : Vector N,
        ‖m‖ ^ 2 = (N : ℝ) * q → ‖m'‖ ^ 2 = (N : ℝ) * q →
        |replicatedBandPressure k μ β q δ ρ J m -
          replicatedBandPressure k μ β q δ ρ J m'| ≤
            L * ‖m - m'‖ / Real.sqrt (N : ℝ)

private theorem uniformDeviationEvent_measurable_of_continuous
    {N k : ℕ} (μ : FiniteMixture) (β q δ ρ t : ℝ)
    (hcontinuous : ∀ m : Vector N,
      Continuous (fun J : Disorder N μ.maxDegree =>
        replicatedBandPressure k μ β q δ ρ J m)) :
    MeasurableSet (uniformDeviationEvent (N := N) k μ β q δ ρ t) := by
  let A (r : ℚ) : Set (Disorder N μ.maxDegree) :=
    ⋂ m : Vector N, ⋂ (_ : ‖m‖ ^ 2 = (N : ℝ) * q),
      {J | |replicatedBandPressure k μ β q δ ρ J m -
        expectedReplicatedBandPressure k μ β q δ ρ m| ≤ (r : ℝ)}
  have hA (r : ℚ) : IsClosed (A r) := by
    exact isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_le ((hcontinuous m).sub continuous_const).abs continuous_const
  have heq : uniformDeviationEvent (N := N) k μ β q δ ρ t =
      ⋃ r : {r : ℚ // (r : ℝ) < t}, A r.val := by
    ext J
    constructor
    · rintro ⟨s, hs, hbound⟩
      obtain ⟨r, hsr, hrt⟩ := exists_rat_btwn hs
      refine Set.mem_iUnion.mpr ⟨⟨r, hrt⟩, ?_⟩
      simp only [A, Set.mem_iInter, Set.mem_ofPred_eq]
      intro m hm
      exact (hbound m hm).trans hsr.le
    · intro hJ
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hJ
      refine ⟨(r.val : ℝ), r.property, ?_⟩
      simpa only [A, Set.mem_iInter, Set.mem_ofPred_eq] using hr
  rw [heq]
  exact MeasurableSet.iUnion fun r => (hA r.val).measurableSet

private theorem exists_nonnegative_physical_center_net
    (N : ℕ) (hN : 0 < N) {q θ : ℝ} (hq : 0 ≤ q) (hθ : 0 < θ) :
    ∃ (M : ℕ) (points : Fin M → Vector N), 0 < M ∧
      (∀ j, ‖points j‖ = Real.sqrt (N : ℝ) * Real.sqrt q) ∧
      (∀ m : Vector N,
        ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt q →
          ∃ j, ‖m - points j‖ ≤ θ * Real.sqrt (N : ℝ)) ∧
      Real.log (M : ℝ) ≤
        (N : ℝ) * Real.log (1 + 2 * Real.sqrt q / θ) := by
  by_cases hqzero : q = 0
  · subst q
    refine ⟨1, fun _ => 0, by omega, by simp, ?_, by simp⟩
    intro m hm
    have hmzero : m = 0 := norm_eq_zero.mp (by simpa using hm)
    refine ⟨0, ?_⟩
    simp only [hmzero, sub_self, norm_zero]
    positivity
  · exact SourcePureCaptureReplicaNetGeometry.exists_physical_center_net N hN
      (lt_of_le_of_ne hq (Ne.symm hqzero)) hθ

/-- The net and union-bound part of Subag's Proposition 24, preserving its
strict event, all finite dimensions `N ≥ k+1`, and original quantifier order.
This modular form separates the three analytic steps, which are discharged
by the subsequent Gaussian and rotation lemmas. -/
private theorem proposition24_of_fixed_center_inputs (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1)
    (hcontinuous : FixedCenterContinuity μ β q)
    (hfixed : FixedCenterConcentration μ β q)
    (hcenter : CenterLipschitzControl μ β q) :
    Proposition24 μ β q := by
  refine ⟨hβ, hq, ?_⟩
  intro t c ht hc
  obtain ⟨L, hL, hmodulus⟩ := hcenter (c + 1) (by linarith)
  let θ : ℝ := t / (4 * L)
  have hθ : 0 < θ := div_pos ht (by positivity)
  let H : ℝ := Real.log (1 + 2 * Real.sqrt q / θ)
  have hH : 0 ≤ H := Real.log_nonneg (by
    have hh : 0 ≤ 2 * Real.sqrt q / θ := by positivity
    linarith)
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, k₀, hpoint⟩ :=
    hfixed (t / 2) (c + H + 1) (by linarith) (by linarith)
  refine ⟨δ₀, hδ₀, ρ₀, hρ₀, max k₀ 1, ?_⟩
  intro δ hδ hδbound ρ hρ hρbound k hk N hN
  have hk₀ : k₀ ≤ k := (Nat.le_max_left k₀ 1).trans hk
  have hkone : 1 ≤ k := (Nat.le_max_right k₀ 1).trans hk
  have hNtwo : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hnorm (m : Vector N) (hm : ‖m‖ ^ 2 = (N : ℝ) * q) :
      ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt q := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hNr.le, Real.sq_sqrt hq.1]
    exact hm
  obtain ⟨M, points, hM, hpoints, hcover, hcard⟩ :=
    exists_nonnegative_physical_center_net N hNpos hq.1 hθ
  have hpointnorm (j : Fin M) : ‖points j‖ ^ 2 = (N : ℝ) * q := by
    rw [hpoints, mul_pow, Real.sq_sqrt hNr.le, Real.sq_sqrt hq.1]
  obtain ⟨Ω, _hΩ, hΩprob, hLip⟩ := hmodulus N hNtwo
  let Bad (j : Fin M) : Set (Disorder N μ.maxDegree) :=
    {J | t / 2 < |replicatedBandPressure k μ β q δ ρ J (points j) -
      expectedReplicatedBandPressure k μ β q δ ρ (points j)|}
  have hsubset : (uniformDeviationEvent (N := N) k μ β q δ ρ t)ᶜ ⊆
      Ωᶜ ∪ ⋃ j : Fin M, Bad j := by
    intro J hJ
    by_contra hbad
    have hgood : J ∈ Ω := by
      by_contra hnot
      exact hbad (Or.inl hnot)
    have hnetgood (j : Fin M) :
        |replicatedBandPressure k μ β q δ ρ J (points j) -
          expectedReplicatedBandPressure k μ β q δ ρ (points j)| ≤ t / 2 := by
      by_contra hnot
      exact hbad (Or.inr (Set.mem_iUnion.mpr ⟨j, not_le.mp hnot⟩))
    apply hJ
    refine ⟨3 * t / 4, by linarith, ?_⟩
    intro m hm
    obtain ⟨j, hj⟩ := hcover m (hnorm m hm)
    have hvariation :
        |replicatedBandPressure k μ β q δ ρ J m -
          replicatedBandPressure k μ β q δ ρ J (points j)| ≤ t / 4 := by
      calc
        _ ≤ L * ‖m - points j‖ / Real.sqrt (N : ℝ) :=
          hLip J hgood k δ ρ m (points j) hm (hpointnorm j)
        _ ≤ L * (θ * Real.sqrt (N : ℝ)) / Real.sqrt (N : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj hL.le) hsqrt.le
        _ = t / 4 := by
          dsimp [θ]
          field_simp
    have hmean : expectedReplicatedBandPressure k μ β q δ ρ m =
        expectedReplicatedBandPressure k μ β q δ ρ (points j) :=
      SourceMixedBandsLiteral.replicated_band_expected_center_independent k μ β q δ ρ
        m (points j) (by rw [hnorm m hm, hpoints j])
    calc
      _ = |(replicatedBandPressure k μ β q δ ρ J m -
          replicatedBandPressure k μ β q δ ρ J (points j)) +
          (replicatedBandPressure k μ β q δ ρ J (points j) -
            expectedReplicatedBandPressure k μ β q δ ρ (points j))| := by
        rw [hmean]
        congr 1
        ring
      _ ≤ |replicatedBandPressure k μ β q δ ρ J m -
          replicatedBandPressure k μ β q δ ρ J (points j)| +
          |replicatedBandPressure k μ β q δ ρ J (points j) -
            expectedReplicatedBandPressure k μ β q δ ρ (points j)| := abs_add_le _ _
      _ ≤ 3 * t / 4 := by linarith [hnetgood j]
  have hbadpoint (j : Fin M) :
      (disorderLaw N μ.maxDegree).real (Bad j) ≤
        Real.exp (-(c + H + 1) * (N : ℝ)) :=
    hpoint δ hδ hδbound ρ hρ hρbound k hk₀ N hN (points j) (hpointnorm j)
  have hbadunion : (disorderLaw N μ.maxDegree).real (⋃ j : Fin M, Bad j) ≤
      (M : ℝ) * Real.exp (-(c + H + 1) * (N : ℝ)) := by
    calc
      _ ≤ ∑ j : Fin M, (disorderLaw N μ.maxDegree).real (Bad j) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin M, Real.exp (-(c + H + 1) * (N : ℝ)) :=
        Finset.sum_le_sum (fun j _ => hbadpoint j)
      _ = _ := by simp
  have hcardexp : (M : ℝ) ≤ Real.exp ((N : ℝ) * H) :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hM)).mp hcard
  have hbadunion' : (disorderLaw N μ.maxDegree).real (⋃ j : Fin M, Bad j) ≤
      Real.exp (-(c + 1) * (N : ℝ)) := by
    calc
      _ ≤ (M : ℝ) * Real.exp (-(c + H + 1) * (N : ℝ)) := hbadunion
      _ ≤ Real.exp ((N : ℝ) * H) * Real.exp (-(c + H + 1) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hcardexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hfailure : (disorderLaw N μ.maxDegree).real
      (uniformDeviationEvent (N := N) k μ β q δ ρ t)ᶜ ≤
        2 * Real.exp (-(c + 1) * (N : ℝ)) := by
    calc
      _ ≤ (disorderLaw N μ.maxDegree).real (Ωᶜ ∪ ⋃ j : Fin M, Bad j) :=
        measureReal_mono hsubset
      _ ≤ (disorderLaw N μ.maxDegree).real Ωᶜ +
          (disorderLaw N μ.maxDegree).real (⋃ j : Fin M, Bad j) :=
        measureReal_union_le _ _
      _ ≤ _ := by linarith
  have hstrict : 2 * Real.exp (-(c + 1) * (N : ℝ)) <
      Real.exp (-c * (N : ℝ)) := by
    have htwo : (2 : ℝ) < Real.exp (N : ℝ) :=
      Real.exp_one_gt_two.trans_le (Real.exp_le_exp.mpr hNone)
    calc
      _ < Real.exp (N : ℝ) * Real.exp (-(c + 1) * (N : ℝ)) :=
        mul_lt_mul_of_pos_right htwo (Real.exp_pos _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmeas := uniformDeviationEvent_measurable_of_continuous μ β q δ ρ t
    (hcontinuous N k δ ρ)
  refine ⟨hmeas, ?_⟩
  have hcompl := measureReal_compl (μ := disorderLaw N μ.maxDegree) hmeas
  simp only [probReal_univ] at hcompl
  linarith [hfailure.trans_lt hstrict]

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagProposition24
open scoped Topology BigOperators
set_option autoImplicit false

/-- At a fixed physical center the literal replicated-band pressure is
continuous in the original disorder, including zero-volume bands. -/
private theorem fixedCenter_pressure_continuous {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β q δ ρ : ℝ) (m : Vector N) :
    Continuous (fun J : Disorder N μ.maxDegree =>
      replicatedBandPressure k μ β q δ ρ J m) := by
  let ν := (Measure.pi (fun _ : Fin k => sphereLaw N)).restrict
    (ReplicatedBand k q δ ρ m)
  let L : (Fin k → Vector N) → EuclideanDisorder N μ.maxDegree →L[ℝ] ℝ :=
    fun σ => β • ∑ i : Fin k,
      (sphereLinear (mixtureCoefficients μ) (σ i) - sphereLinear (mixtureCoefficients μ) m)
  let K : ℝ := |β| * (k : ℝ) *
    (Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) +
      ‖sphereLinear (mixtureCoefficients μ) m‖)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : Measurable L := by
    have hs : Measurable (fun σ : Fin k → Vector N => ∑ i : Fin k,
        (sphereLinear (mixtureCoefficients μ) (σ i) -
          sphereLinear (mixtureCoefficients μ) m)) := by
      apply Finset.measurable_sum
      intro i _
      exact ((sphereLinear_measurable _).comp (measurable_pi_apply i)).sub measurable_const
    exact (measurable_const : Measurable (fun _ : Fin k → Vector N => β)).smul hs
  have ha : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw N), ∀ i : Fin k,
      ‖sphereLinear (mixtureCoefficients μ) (σ i)‖ ≤
        Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) :=
    eventually_all.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin k => sphereLaw N) (i := i)).eventually
        (sphereLinear_bound hN _ (mixtureCoefficients_nonnegative μ)))
  have hb : ∀ᵐ σ ∂ν, ‖L σ‖ ≤ K := by
    filter_upwards [ha.filter_mono ae_restrict_le] with σ hσ
    dsimp [L, K]
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
    calc
      _ ≤ ∑ i : Fin k,
          ‖sphereLinear (mixtureCoefficients μ) (σ i) -
            sphereLinear (mixtureCoefficients μ) m‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k,
          (Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) +
            ‖sphereLinear (mixtureCoefficients μ) m‖) := by
        apply Finset.sum_le_sum
        intro i _
        exact (norm_sub_le _ _).trans (add_le_add (hσ i) (le_refl _))
      _ = _ := by simp; ring
  have he (J : Disorder N μ.maxDegree) :
      GaussianSpinInterpolation.logPartition ν L (euclideanDisorder J) =
        Real.log (replicatedBandPartition k μ β q δ ρ J m) := by
    unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
    congr 1
    apply integral_congr_ae
    exact .of_forall fun σ => by
      simp only [GaussianSpinInterpolation.weight, one_mul, L,
        _root_.smul_apply, _root_.sum_apply,
        _root_.sub_apply, smul_eq_mul, sphereLinear_apply,
        unpack_euclideanDisorder]
  by_cases hz : ν = 0
  · have hp (J : Disorder N μ.maxDegree) :
        replicatedBandPartition k μ β q δ ρ J m = 0 := by
      change (∫ σ, Real.exp (β * ∑ i : Fin k,
        (field (mixtureCoefficients μ) J (σ i) -
          field (mixtureCoefficients μ) J m)) ∂ν) = 0
      rw [hz, integral_zero_measure]
    simpa only [replicatedBandPressure, hp, Real.log_zero, zero_div] using
      (continuous_const : Continuous (fun _ : Disorder N μ.maxDegree => (0 : ℝ)))
  · let : NeZero ν := ⟨hz⟩
    have hcont : Continuous (euclideanDisorder (N := N) (P := μ.maxDegree)) := by
      exact (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Coordinate N μ.maxDegree => ℝ)).symm.continuous.comp
          (continuous_pi fun z => (continuous_apply z.2).comp (continuous_apply z.1))
    have hc := (GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).continuous.comp hcont
    simpa only [Function.comp_def, he, replicatedBandPressure] using
      hc.div_const ((N : ℝ) * (k : ℝ))

/-- The fixed-center Gaussian step in Subag's Section 3, at the literal
original-disorder expectation. -/
private theorem fixedCenter_concentration_of_euclidean_lipschitz {N k : ℕ}
    (μ : FiniteMixture) (β q δ ρ : ℝ) (m : Vector N) {L t : ℝ}
    (hL : 0 < L) (ht : 0 < t)
    (hLip : LipschitzWith L.toNNReal
      (fun g : EuclideanDisorder N μ.maxDegree =>
        replicatedBandPressure k μ β q δ ρ (unpackDisorder g) m)) :
    disorderLaw N μ.maxDegree {J |
      |replicatedBandPressure k μ β q δ ρ J m -
        expectedReplicatedBandPressure k μ β q δ ρ m| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  let F := fun g : EuclideanDisorder N μ.maxDegree =>
    replicatedBandPressure k μ β q δ ρ (unpackDisorder g) m
  have hlaw := euclideanDisorder_hasLaw N μ.maxDegree
  have hmean : expectedReplicatedBandPressure k μ β q δ ρ m =
      ∫ g, F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree) := by
    exact hlaw.integral_comp hLip.continuous.aestronglyMeasurable
  have h := SYK.euclidean_lipschitz_gaussian_concentration F L t hL ht hLip
  have hset : MeasurableSet {g : EuclideanDisorder N μ.maxDegree |
      |F g - (∫ y, F y ∂SYK.standardGaussianMeasureOnEuclidean
        (Coordinate N μ.maxDegree))| > t} :=
    (isOpen_lt continuous_const (hLip.continuous.sub continuous_const).abs).measurableSet
  nth_rw 1 [← hlaw.map_eq] at h
  rw [Measure.map_apply_of_aemeasurable hlaw.aemeasurable hset] at h
  rw [hmean]
  simpa only [Set.preimage_ofPred_eq, F, unpack_euclideanDisorder] using h

/-- Fixed-center disorder continuity holds in every dimension; dimension
zero is the pressure's literal zero-denominator case. -/
private theorem fixedCenterContinuity (μ : FiniteMixture) (β q : ℝ) :
    FixedCenterContinuity μ β q := by
  intro N k δ ρ m
  by_cases hN : N = 0
  · subst N
    simpa only [replicatedBandPressure, Nat.cast_zero, zero_mul, div_zero] using
      (continuous_const : Continuous (fun _ : Disorder 0 μ.maxDegree => (0 : ℝ)))
  · exact fixedCenter_pressure_continuous (by omega) μ β q δ ρ m

/-- Continuity is discharged from the three-step net reduction. The two
inputs are the fixed-center Gaussian estimate and center rotation. -/
private theorem proposition24_of_concentration_and_center_control (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1)
    (hfixed : FixedCenterConcentration μ β q)
    (hcenter : CenterLipschitzControl μ β q) : Proposition24 μ β q :=
  proposition24_of_fixed_center_inputs μ hβ hq (fixedCenterContinuity μ β q) hfixed hcenter

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel LiteratureSubagPhysicalDefinitions
open scoped Topology BigOperators RealInnerProductSpace
set_option autoImplicit false

private theorem finite_logPartition_lipschitz {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] (ν : Measure V) [IsFiniteMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    LipschitzWith K.toNNReal (GaussianSpinInterpolation.logPartition ν L) := by
  by_cases hz : ν = 0
  · apply LipschitzWith.of_dist_le_mul
    intro g h
    simp only [hz, GaussianSpinInterpolation.logPartition,
      GaussianSpinInterpolation.moment, integral_zero_measure, Real.log_zero,
      dist_self]
    positivity
  · let : NeZero ν := ⟨hz⟩
    apply lipschitzWith_of_nnnorm_fderiv_le
      ((GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).differentiable
        (by norm_num))
    intro w
    rw [(GaussianSpinInterpolation.logPartition_hasFDerivAt ν L hL hK hb w).fderiv]
    apply (NNReal.coe_le_coe).mp
    change ‖GaussianSpinInterpolation.score ν L w‖ ≤ (K.toNNReal : ℝ)
    rw [Real.coe_toNNReal K hK]
    exact GaussianSpinInterpolation.norm_score_le ν L hL hK hb w

private theorem physical_replicatedBand_measurable {N k : ℕ}
    (q δ ρ : ℝ) (m : Vector N) : MeasurableSet (ReplicatedBand k q δ ρ m) := by
  simp only [ReplicatedBand, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun i => measurableSet_le
      (by unfold overlap; fun_prop) measurable_const
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_lt
        (by unfold overlap; fun_prop) measurable_const

/-- The true fixed-center pressure has Subag's small covariance-proxy
Lipschitz constant in Euclidean disorder coordinates. -/
private theorem fixedCenter_pressure_euclidean_lipschitz {N k : ℕ}
    (hN : 0 < N) (hk : 0 < k) (μ : FiniteMixture) (β : ℝ)
    {q δ ρ : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (m : Vector N) (hm : ‖m‖ ^ 2 = (N : ℝ) * q) :
    LipschitzWith
      (|β| * Real.sqrt ((N : ℝ) * ((k : ℝ) * μ.xi 1 +
        μ.xi1 1 * (k : ℝ) ^ 2 * (ρ + 2 * δ))) /
          ((N : ℝ) * (k : ℝ))).toNNReal
      (fun g : EuclideanDisorder N μ.maxDegree =>
        replicatedBandPressure k μ β q δ ρ (unpackDisorder g) m) := by
  let ν := (Measure.pi (fun _ : Fin k => sphereLaw N)).restrict
    (ReplicatedBand k q δ ρ m)
  let L : (Fin k → Vector N) → EuclideanDisorder N μ.maxDegree →L[ℝ] ℝ :=
    fun σ => β • ∑ i : Fin k,
      (sphereLinear (mixtureCoefficients μ) (σ i) - sphereLinear (mixtureCoefficients μ) m)
  let A : ℝ := (N : ℝ) * ((k : ℝ) * μ.xi 1 +
    μ.xi1 1 * (k : ℝ) ^ 2 * (ρ + 2 * δ))
  let K : ℝ := |β| * Real.sqrt A
  let D : ℝ := (N : ℝ) * (k : ℝ)
  have hxi : 0 ≤ μ.xi 1 := xi_nonneg μ zero_le_one
  have hxi1 : 0 ≤ μ.xi1 1 := xi1_one_nonneg μ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 < D := mul_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hk)
  have hL : Measurable L := by
    have hs : Measurable (fun σ : Fin k → Vector N => ∑ i : Fin k,
        (sphereLinear (mixtureCoefficients μ) (σ i) -
          sphereLinear (mixtureCoefficients μ) m)) := by
      apply Finset.measurable_sum
      intro i _
      exact ((sphereLinear_measurable _).comp (measurable_pi_apply i)).sub measurable_const
    exact (measurable_const : Measurable (fun _ : Fin k → Vector N => β)).smul hs
  have ha : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw N), ∀ i : Fin k,
      ‖σ i‖ ^ 2 = (N : ℝ) :=
    eventually_all.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin k => sphereLaw N) (i := i)).eventually
        (sphereLaw_support (by omega : 1 ≤ N)))
  have hb : ∀ᵐ σ ∂ν, ‖L σ‖ ≤ K := by
    filter_upwards [ha.filter_mono ae_restrict_le,
      ae_restrict_mem (physical_replicatedBand_measurable q δ ρ m)] with σ hσ hband
    have hnorm := replicatedFeature_norm_sq_le hN μ hq hδ hρ m hm σ hσ hband
    have hroot : ‖replicatedFeature k μ m σ‖ ≤ Real.sqrt A := by
      have hsq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
      have hn := norm_nonneg (replicatedFeature k μ m σ)
      have hs := Real.sqrt_nonneg A
      change ‖replicatedFeature k μ m σ‖ ^ 2 ≤ A at hnorm
      nlinarith
    have heq : (∑ i : Fin k,
        (sphereLinear (mixtureCoefficients μ) (σ i) -
          sphereLinear (mixtureCoefficients μ) m)) =
        innerSL ℝ (replicatedFeature k μ m σ) := by
      simp only [replicatedFeature, map_sum, map_sub, sphereLinear]
    dsimp only [L, K]
    rw [norm_smul, Real.norm_eq_abs, heq, innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_left hroot (abs_nonneg β)
  have he (g : EuclideanDisorder N μ.maxDegree) :
      GaussianSpinInterpolation.logPartition ν L g =
        Real.log (replicatedBandPartition k μ β q δ ρ (unpackDisorder g) m) := by
    unfold GaussianSpinInterpolation.logPartition GaussianSpinInterpolation.moment
    congr 1
    apply integral_congr_ae
    exact .of_forall fun σ => by
      simp only [GaussianSpinInterpolation.weight, one_mul, L,
        _root_.smul_apply, _root_.sum_apply,
        _root_.sub_apply, smul_eq_mul, sphereLinear_apply]
  have hLip := finite_logPartition_lipschitz ν L hL hK hb
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [Real.dist_eq, Real.coe_toNNReal _ (div_nonneg hK hD.le)]
  have hd := hLip.dist_le_mul g h
  rw [Real.dist_eq, Real.coe_toNNReal _ hK] at hd
  change |Real.log (replicatedBandPartition k μ β q δ ρ (unpackDisorder g) m) / D -
    Real.log (replicatedBandPartition k μ β q δ ρ (unpackDisorder h) m) / D| ≤
      K / D * dist g h
  rw [← he g, ← he h, ← sub_div, abs_div, abs_of_pos hD]
  exact (div_le_div_of_nonneg_right hd hD.le).trans_eq (by ring)

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory Set SphericalModel LiteratureSubagPhysicalDefinitions
open LiteratureSubagProposition24 SourceMixedBandsLiteral.BallLipschitz
set_option autoImplicit false

/-- The deterministic center-rotation estimate used in the net argument. Its only random
quantity is the actual Lipschitz constant of the Hamiltonian on the ball. -/
private def ReplicatedPressureRotationEstimate (μ : FiniteMixture) (β q : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ J : Disorder N μ.maxDegree, ∀ k : ℕ, ∀ δ ρ : ℝ,
    ∀ m m' : Vector N,
      ‖m‖ ^ 2 = (N : ℝ) * q → ‖m'‖ ^ 2 = (N : ℝ) * q →
      |replicatedBandPressure k μ β q δ ρ J m -
        replicatedBandPressure k μ β q δ ρ J m'| ≤
          A * physicalBallLipschitzConstant (mixtureCoefficients μ) J *
            ‖m - m'‖ / (N : ℝ)

/-- The proved arbitrary-rate form of Lemma 17 supplies the probabilistic
center modulus once the deterministic rotation comparison is known. -/
private theorem centerLipschitzControl_of_rotationEstimate (μ : FiniteMixture) (β q : ℝ)
    (hrot : ReplicatedPressureRotationEstimate μ β q) :
    CenterLipschitzControl μ β q := by
  obtain ⟨A, hA, hrotation⟩ := hrot
  intro c hc
  obtain ⟨C, hC, htail⟩ := physicalBallLipschitz_arbitrary_rate μ hc
  refine ⟨A * C, mul_pos hA hC, ?_⟩
  intro N hN
  obtain ⟨hBad, hBadprob⟩ := htail N hN
  refine ⟨{J : Disorder N μ.maxDegree |
    C * Real.sqrt (N : ℝ) < physicalBallLipschitzConstant (mixtureCoefficients μ) J}ᶜ,
    hBad.compl, ?_, ?_⟩
  · simpa only [compl_compl] using hBadprob
  · intro J hJ k δ ρ m m' hm hm'
    have hJLip : physicalBallLipschitzConstant (mixtureCoefficients μ) J ≤
        C * Real.sqrt (N : ℝ) := le_of_not_gt hJ
    have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
    calc
      _ ≤ A * physicalBallLipschitzConstant (mixtureCoefficients μ) J *
          ‖m - m'‖ / (N : ℝ) := hrotation N hN J k δ ρ m m' hm hm'
      _ ≤ A * (C * Real.sqrt (N : ℝ)) * ‖m - m'‖ / (N : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJLip hA.le)
            (norm_nonneg _)) hNr.le
      _ = (A * C) * ‖m - m'‖ / Real.sqrt (N : ℝ) := by
        apply (div_eq_div_iff hNr.ne' hsqrt.ne').mpr
        calc
          _ = A * C * ‖m - m'‖ * (Real.sqrt (N : ℝ)) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hNr.le]

/-- The exact Proposition 24 interface is reduced to fixed-center Gaussian
tails and the deterministic rotation comparison. No Parisi formula is used. -/
private theorem proposition24_of_concentration_and_rotation_estimate
    (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1)
    (hfixed : FixedCenterConcentration μ β q)
    (hrot : ReplicatedPressureRotationEstimate μ β q) :
    Proposition24 μ β q :=
  proposition24_of_concentration_and_center_control μ hβ hq hfixed
    (centerLipschitzControl_of_rotationEstimate μ β q hrot)

/-- At zero squared center radius there is just one center, so no rotation
estimate or exceptional Lipschitz event is needed. -/
private theorem centerLipschitzControl_zero (μ : FiniteMixture) (β : ℝ) :
    CenterLipschitzControl μ β 0 := by
  intro c _hc
  refine ⟨1, by norm_num, ?_⟩
  intro N _hN
  refine ⟨univ, MeasurableSet.univ, ?_, ?_⟩
  · simp only [compl_univ, measureReal_empty]
    exact (Real.exp_pos _).le
  · intro J _hJ k δ ρ m m' hm hm'
    have hmzero : m = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg m])
    have hm'zero : m' = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg m'])
    simp [hmzero, hm'zero]

/-- The singleton-center case of Proposition 24, with only the
fixed-center Gaussian input still exposed. -/
private theorem proposition24_zero_of_fixedCenterConcentration (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 < β) (hfixed : FixedCenterConcentration μ β 0) :
    Proposition24 μ β 0 :=
  proposition24_of_concentration_and_center_control μ hβ ⟨le_rfl, zero_lt_one⟩ hfixed
    (centerLipschitzControl_zero μ β)

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Set
open SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagProposition24
open scoped BigOperators
set_option autoImplicit false

private theorem exists_small_replica_variance_proxy (A B : ℝ) (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ k₀ : ℕ,
      1 ≤ k₀ ∧ ∀ δ ρ : ℝ, δ ≤ δ₀ → ρ ≤ ρ₀ →
      ∀ k : ℕ, k₀ ≤ k → A / (k : ℝ) + B * (ρ + 2 * δ) ≤ ε := by
  let d : ℝ := ε / (6 * (B + 1))
  have hd : 0 < d := div_pos hε (by positivity)
  have heq : 6 * (B + 1) * d = ε := by
    dsimp [d]
    field_simp
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * A / ε)
  refine ⟨d, hd, d, hd, max n 1, Nat.le_max_right n 1, ?_⟩
  intro δ ρ hδ hρ k hk
  have hkone : 1 ≤ k := (Nat.le_max_right n 1).trans hk
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk : (n : ℝ) ≤ k := by exact_mod_cast ((Nat.le_max_left n 1).trans hk)
  have hAk : 2 * A ≤ ε * (k : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp (hn.trans_le hnk)
    linarith
  have hfrac : A / (k : ℝ) ≤ ε / 2 :=
    (div_le_iff₀ hkpos).mpr (by linarith)
  have hBd : B * d ≤ ε / 6 := by nlinarith [hd.le]
  have hBδ := mul_le_mul_of_nonneg_left hδ hB
  have hBρ := mul_le_mul_of_nonneg_left hρ hB
  linarith

/-- The fixed-center concentration input is a theorem for the literal
physical replicated bands. Small tolerances and many replicas give every
prescribed exponential rate, uniformly for all `N ≥ k+1`. -/
private theorem fixedCenterConcentration (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) :
    FixedCenterConcentration μ β q := by
  intro t c ht hc
  let ε : ℝ := t ^ 2 / (2 * β ^ 2 * (c + 1))
  have hε : 0 < ε := div_pos (sq_pos_of_pos ht) (by positivity)
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, k₀, hk₀, hsmall⟩ :=
    exists_small_replica_variance_proxy (μ.xi 1) (μ.xi1 1) (xi1_one_nonneg μ) hε
  refine ⟨δ₀, hδ₀, ρ₀, hρ₀, k₀, ?_⟩
  intro δ hδ hδbound ρ hρ hρbound k hk N hN m hm
  have hkone : 1 ≤ k := hk₀.trans hk
  have hkpos : 0 < k := by omega
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hkr : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hxi : 0 < μ.xi 1 := μ.xi_pos zero_lt_one
  have hxi1 : 0 ≤ μ.xi1 1 := xi1_one_nonneg μ
  let P : ℝ := μ.xi 1 / (k : ℝ) + μ.xi1 1 * (ρ + 2 * δ)
  let A : ℝ := (N : ℝ) * ((k : ℝ) * μ.xi 1 +
    μ.xi1 1 * (k : ℝ) ^ 2 * (ρ + 2 * δ))
  let L : ℝ := |β| * Real.sqrt A / ((N : ℝ) * (k : ℝ))
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := div_pos (mul_pos (abs_pos.mpr hβ.ne')
    (Real.sqrt_pos.mpr hA)) (mul_pos hNr hkr)
  have hLsq : (N : ℝ) * L ^ 2 = β ^ 2 * P := by
    dsimp [L, P]
    rw [div_pow, mul_pow, sq_abs, Real.sq_sqrt hA.le]
    dsimp [A]
    field_simp [hNr.ne', hkr.ne']
  have hP : P ≤ ε := hsmall δ ρ hδbound hρbound k hk
  have hεeq : 2 * (c + 1) * (β ^ 2 * ε) = t ^ 2 := by
    dsimp [ε]
    field_simp
  have hprod : (c + 1) * (N : ℝ) * (2 * L ^ 2) ≤ t ^ 2 := by
    calc
      _ = 2 * (c + 1) * (β ^ 2 * P) := by rw [← hLsq]; ring
      _ ≤ 2 * (c + 1) * (β ^ 2 * ε) := by
        gcongr
      _ = _ := hεeq
  have hexponent : -t ^ 2 / (2 * L ^ 2) ≤ -(c + 1) * (N : ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * L ^ 2)).mpr hprod
    simpa only [neg_div, neg_mul] using neg_le_neg hh
  have hLip := fixedCenter_pressure_euclidean_lipschitz hNpos hkpos μ β hq hδ.le hρ.le m hm
  have hgauss := fixedCenter_concentration_of_euclidean_lipschitz
    μ β q δ ρ m hL ht hLip
  have hreal : (disorderLaw N μ.maxDegree).real
      {J | t < |replicatedBandPressure k μ β q δ ρ J m -
        expectedReplicatedBandPressure k μ β q δ ρ m|} ≤
      2 * Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgauss
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity :
      0 ≤ 2 * Real.exp (-t ^ 2 / (2 * L ^ 2)))] using hh
  have htwo : (2 : ℝ) < Real.exp (N : ℝ) :=
    Real.exp_one_gt_two.trans_le (Real.exp_le_exp.mpr hNone)
  calc
    _ ≤ 2 * Real.exp (-t ^ 2 / (2 * L ^ 2)) := hreal
    _ ≤ 2 * Real.exp (-(c + 1) * (N : ℝ)) := by gcongr
    _ ≤ Real.exp (N : ℝ) * Real.exp (-(c + 1) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right htwo.le (Real.exp_pos _).le
    _ = Real.exp (-c * (N : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel LiteratureSubagProposition24 SphericalTAPCertificate
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceReductionConsumerAsymptotic SphericalOrthogonalHaar
open SphericalRotationCovariance SphericalReversibility SphericalDynamics
open SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v

/-- The fixed-center and deterministic-rotation steps imply the original
Proposition 24 interface with its exact strict event and quantifier order. -/
private theorem proposition24_reduced (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1)
    (hrot : ReplicatedPressureRotationEstimate μ β q) :
    Proposition24 μ β q :=
  proposition24_of_concentration_and_rotation_estimate μ hβ hq
    (fixedCenterConcentration μ hβ hq) hrot

/-- Proposition 24 is completely proved when the center radius is zero.
This uses no literature hypotheses or deterministic rotation premise. -/
private theorem proposition24_zero (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) :
    Proposition24 μ β 0 :=
  proposition24_zero_of_fixedCenterConcentration μ hβ
    (fixedCenterConcentration μ hβ ⟨le_rfl, zero_lt_one⟩)



end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof

open SphericalModel
open scoped RealInnerProductSpace
set_option autoImplicit false

private theorem normalized_vector_difference_le {N : ℕ} {u v : Vector N}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ≤ 2 * ‖u - v‖ / ‖v‖ := by
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have he : ‖u‖⁻¹ • u - ‖v‖⁻¹ • v =
      (‖u‖⁻¹ - ‖v‖⁻¹) • u + ‖v‖⁻¹ • (u - v) := by module
  have hc : |‖u‖⁻¹ - ‖v‖⁻¹| * ‖u‖ = |‖v‖ - ‖u‖| / ‖v‖ := by
    rw [inv_sub_inv hun.ne' hvn.ne', abs_div, abs_mul,
      abs_of_pos hun, abs_of_pos hvn]
    field_simp
  calc
    _ ≤ ‖(‖u‖⁻¹ - ‖v‖⁻¹) • u‖ + ‖‖v‖⁻¹ • (u - v)‖ := by
      rw [he]
      exact norm_add_le _ _
    _ = |‖v‖ - ‖u‖| / ‖v‖ + ‖u - v‖ / ‖v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        hc, abs_inv, abs_of_pos hvn]
      ring
    _ ≤ _ := by
      have hn := abs_norm_sub_norm_le v u
      rw [norm_sub_rev v u] at hn
      have hh := div_le_div_of_nonneg_right hn hvn.le
      calc
        |‖v‖ - ‖u‖| / ‖v‖ + ‖u - v‖ / ‖v‖ ≤
            ‖u - v‖ / ‖v‖ + ‖u - v‖ / ‖v‖ := add_le_add hh le_rfl
        _ = 2 * ‖u - v‖ / ‖v‖ := by ring

private theorem unit_hyperplane_reflection_difference_le {N : ℕ}
    (a b x : Vector N) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖(ℝ ∙ a)ᗮ.reflection x - (ℝ ∙ b)ᗮ.reflection x‖ ≤
      4 * ‖a - b‖ * ‖x‖ := by
  have he : (ℝ ∙ a)ᗮ.reflection x - (ℝ ∙ b)ᗮ.reflection x =
      (2 * inner ℝ a x) • (b - a) +
        (2 * inner ℝ (b - a) x) • b := by
    rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_orthogonal_apply,
      Submodule.reflection_singleton_apply, Submodule.reflection_singleton_apply,
      ha, hb]
    simp only [inner_sub_left]
    module
  have hia := abs_real_inner_le_norm a x
  rw [ha, one_mul] at hia
  have hib := abs_real_inner_le_norm (b - a) x
  rw [norm_sub_rev b a] at hib
  calc
    _ ≤ ‖(2 * inner ℝ a x) • (b - a)‖ +
        ‖(2 * inner ℝ (b - a) x) • b‖ := by
      rw [he]
      exact norm_add_le _ _
    _ = 2 * |inner ℝ a x| * ‖a - b‖ +
        2 * |inner ℝ (b - a) x| := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        norm_sub_rev b a, hb, mul_one]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hia (norm_nonneg (a - b))
      nlinarith

/-- Equal nonzero center radii have an orthogonal transport whose point
movement is bounded by the relative center movement. -/
private theorem exists_small_displacement_center_isometry {N : ℕ}
    (m m' : Vector N) (hm : m ≠ 0) (hnorm : ‖m‖ = ‖m'‖) :
    ∃ U : Vector N ≃ₗᵢ[ℝ] Vector N, U m = m' ∧
      ∀ x : Vector N, ‖U x - x‖ ≤ 16 * ‖x‖ * ‖m - m'‖ / ‖m‖ := by
  have hmn : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hm'n : 0 < ‖m'‖ := by rw [← hnorm]; exact hmn
  have hm' : m' ≠ 0 := norm_pos_iff.mp hm'n
  by_cases hsum : m + m' = 0
  · have heq : m' = -m := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [add_comm] using hsum
    refine ⟨LinearIsometryEquiv.neg ℝ, ?_, ?_⟩
    · change -m = m'
      exact heq.symm
    · intro x
      have hd : ‖m - m'‖ = 2 * ‖m‖ := by
        rw [heq, sub_neg_eq_add, ← two_smul ℝ m, norm_smul]
        norm_num
      have hc : ‖(LinearIsometryEquiv.neg ℝ) x - x‖ ≤ 2 * ‖x‖ := by
        calc
          _ ≤ ‖(LinearIsometryEquiv.neg ℝ) x‖ + ‖x‖ := norm_sub_le _ _
          _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring
      apply (le_div_iff₀ hmn).mpr
      rw [hd]
      have hh := mul_le_mul_of_nonneg_right hc hmn.le
      nlinarith [norm_nonneg x]
  · let w : Vector N := (1 / 2 : ℝ) • (m + m')
    have hw : w ≠ 0 := smul_ne_zero (by norm_num) hsum
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let a : Vector N := ‖w‖⁻¹ • w
    let b : Vector N := ‖m'‖⁻¹ • m'
    have ha : ‖a‖ = 1 := norm_smul_inv_norm hw
    have hb : ‖b‖ = 1 := norm_smul_inv_norm hm'
    have hspanA : ℝ ∙ a = ℝ ∙ (m + m') := by
      dsimp only [a, w]
      rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr
        (inv_ne_zero hwn.ne')),
        Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num))]
    have hspanB : ℝ ∙ b = ℝ ∙ m' := by
      exact Submodule.span_singleton_smul_eq
        (isUnit_iff_ne_zero.mpr (inv_ne_zero hm'n.ne')) m'
    let U : Vector N ≃ₗᵢ[ℝ] Vector N :=
      (ℝ ∙ a)ᗮ.reflection.trans (ℝ ∙ b)ᗮ.reflection
    refine ⟨U, ?_, ?_⟩
    · change (ℝ ∙ b)ᗮ.reflection ((ℝ ∙ a)ᗮ.reflection m) = m'
      simp only [hspanA, hspanB]
      have hr : (ℝ ∙ (m + m'))ᗮ.reflection m = -m' := by
        simpa only [sub_neg_eq_add] using
          (Submodule.reflection_sub (v := m) (w := -m') (by simpa using hnorm))
      rw [hr, map_neg, Submodule.reflection_orthogonalComplement_singleton_eq_neg, neg_neg]
    · intro x
      have he : ‖U x - x‖ =
          ‖(ℝ ∙ a)ᗮ.reflection x - (ℝ ∙ b)ᗮ.reflection x‖ := by
        calc
          _ = ‖(ℝ ∙ b)ᗮ.reflection ((ℝ ∙ a)ᗮ.reflection x) -
              (ℝ ∙ b)ᗮ.reflection ((ℝ ∙ b)ᗮ.reflection x)‖ := by
            rw [Submodule.reflection_reflection]
            rfl
          _ = _ := by rw [← map_sub, LinearIsometryEquiv.norm_map]
      have hab : ‖a - b‖ ≤ ‖m - m'‖ / ‖m‖ := by
        have hn := normalized_vector_difference_le hw hm'
        have hd : w - m' = (1 / 2 : ℝ) • (m - m') := by dsimp [w]; module
        change ‖a - b‖ ≤ 2 * ‖w - m'‖ / ‖m'‖ at hn
        rw [hd, norm_smul, Real.norm_eq_abs, ← hnorm] at hn
        norm_num at hn
        convert hn using 1
        ring
      rw [he]
      calc
        _ ≤ 4 * ‖a - b‖ * ‖x‖ := unit_hyperplane_reflection_difference_le a b x ha hb
        _ ≤ 4 * (‖m - m'‖ / ‖m‖) * ‖x‖ := by gcongr
        _ ≤ 16 * ‖x‖ * ‖m - m'‖ / ‖m‖ := by
          have hh : 0 ≤ ‖m - m'‖ / ‖m‖ * ‖x‖ := by positivity
          calc
            _ = 4 * (‖m - m'‖ / ‖m‖ * ‖x‖) := by ring
            _ ≤ 16 * (‖m - m'‖ / ‖m‖ * ‖x‖) := by linarith
            _ = _ := by ring

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Set Metric Filter
open SphericalModel LiteratureSubagPhysicalDefinitions SourceMixedBandsLiteral.BallLipschitz
open scoped BigOperators
set_option autoImplicit false

private theorem ball_field_lipschitz {N P : ℕ}
    (c : Degree P → ℝ) (J : Disorder N P) :
    LipschitzOnWith ⟨physicalBallLipschitzConstant c J,
      physicalBallLipschitzConstant_nonneg c J⟩
      (field c J) (closedBall 0 (Real.sqrt (N : ℝ))) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (field_contDiff c J).differentiable (by simp) x) _
    (convex_closedBall (0 : Vector N) (Real.sqrt (N : ℝ)))
  intro x hx
  have hb : BddAbove ((fun y => ‖fderiv ℝ (field c J) y‖) ''
      closedBall 0 (Real.sqrt (N : ℝ))) :=
    ((isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).image
      ((field_contDiff c J).fderiv_right (m := ⊤) (by simp)).continuous.norm).bddAbove
  have hh : ‖fderiv ℝ (field c J) x‖ ≤ physicalBallLipschitzConstant c J :=
    le_csSup hb ⟨x, hx, rfl⟩
  exact_mod_cast hh

private theorem tuple_exp_integrable {N k : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H) (m : Vector N) :
    Integrable (fun σ : Fin k → Vector N =>
      Real.exp (β * ∑ i : Fin k, (H (σ i) - H m)))
      (Measure.pi (fun _ : Fin k => sphereLaw N)) := by
  have hi := partitionAgainst_integrable (sphereLaw N) (sphereLaw_support hN) β
    (hH.sub (continuous_const (y := H m)))
  have hh := Integrable.fintype_prod (fun _ : Fin k => hi)
  convert hh using 1
  ext σ
  rw [Finset.mul_sum, Real.exp_sum]
  rfl

private theorem abs_log_integral_exp_sub_le {V : Type*} [MeasurableSpace V]
    (ν : Measure V) (f g : V → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hf : Integrable (fun v => Real.exp (f v)) ν)
    (hg : Integrable (fun v => Real.exp (g v)) ν)
    (hfg : ∀ᵐ v ∂ν, |f v - g v| ≤ D) :
    |Real.log (∫ v, Real.exp (f v) ∂ν) -
      Real.log (∫ v, Real.exp (g v) ∂ν)| ≤ D := by
  by_cases hz : ν = 0
  · simp only [hz, integral_zero_measure, sub_self, abs_zero]
    exact hD
  let : NeZero ν := ⟨hz⟩
  have hfp := integral_exp_pos hf
  have hgp := integral_exp_pos hg
  have hcmp (a b : V → ℝ)
      (ha : Integrable (fun v => Real.exp (a v)) ν)
      (hb : Integrable (fun v => Real.exp (b v)) ν)
      (hab : ∀ᵐ v ∂ν, a v - b v ≤ D) :
      (∫ v, Real.exp (a v) ∂ν) ≤ Real.exp D * ∫ v, Real.exp (b v) ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono_ae ha (hb.const_mul _)
    filter_upwards [hab] with v hv
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hupper := Real.log_le_log hfp (hcmp f g hf hg (hfg.mono fun _ h =>
    (le_abs_self _).trans h))
  have hlower := Real.log_le_log hgp (hcmp g f hg hf (hfg.mono fun v h => by
    linarith [neg_abs_le (f v - g v)]))
  rw [Real.log_mul (Real.exp_ne_zero _) hgp.ne', Real.log_exp] at hupper
  rw [Real.log_mul (Real.exp_ne_zero _) hfp.ne', Real.log_exp] at hlower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem replicatedBandPartition_transport {N k : ℕ}
    (μ : FiniteMixture) (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree)
    (m m' : Vector N) (U : Vector N ≃ₗᵢ[ℝ] Vector N) (hUm : U m = m') :
    replicatedBandPartition k μ β q δ ρ J m' =
      ∫ σ in ReplicatedBand k q δ ρ m,
        Real.exp (β * ∑ i : Fin k,
          (field (mixtureCoefficients μ) J (U (σ i)) -
            field (mixtureCoefficients μ) J m'))
        ∂Measure.pi (fun _ : Fin k => sphereLaw N) := by
  let ν := Measure.pi (fun _ : Fin k => sphereLaw N)
  let T : (Fin k → Vector N) → (Fin k → Vector N) := fun σ i => U (σ i)
  have hT : Measurable T := Measurable.of_eval (fun i =>
    U.continuous.measurable.comp (measurable_pi_apply i))
  have hmap : ν.map T = ν := by
    rw [Measure.pi_map_pi (fun _ : Fin k => U.continuous.measurable.aemeasurable)]
    simp only [sphereLaw_rotation_invariant]
    rfl
  let F := (ReplicatedBand k q δ ρ m').indicator (fun σ =>
    Real.exp (β * ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m')))
  have hF : StronglyMeasurable F := by
    have hc : Continuous (fun σ : Fin k → Vector N =>
        Real.exp (β * ∑ i : Fin k,
          (field (mixtureCoefficients μ) J (σ i) - field (mixtureCoefficients μ) J m'))) := by
      apply Real.continuous_exp.comp
      apply continuous_const.mul
      apply continuous_finsetSum
      intro i _
      exact ((field_contDiff (mixtureCoefficients μ) J).continuous.comp
        (continuous_apply i)).sub continuous_const
    exact hc.stronglyMeasurable.indicator (physical_replicatedBand_measurable q δ ρ m')
  have hchange := integral_map (μ := ν) hT.aemeasurable hF.aestronglyMeasurable
  rw [hmap] at hchange
  unfold replicatedBandPartition
  rw [← integral_indicator (physical_replicatedBand_measurable q δ ρ m'),
    ← integral_indicator (physical_replicatedBand_measurable q δ ρ m)]
  change (∫ σ, F σ ∂ν) = _
  rw [hchange]
  apply integral_congr_ae
  exact ae_of_all _ fun σ => by
    change F (T σ) = _
    have hmem : T σ ∈ ReplicatedBand k q δ ρ m' ↔ σ ∈ ReplicatedBand k q δ ρ m := by
      rw [← hUm]
      simp only [ReplicatedBand, mem_ofPred_eq, T, overlap, U.inner_map_map]
    by_cases hs : σ ∈ ReplicatedBand k q δ ρ m
    · rw [show F (T σ) = _ from Set.indicator_of_mem (hmem.mpr hs) _,
        Set.indicator_of_mem hs]
    · rw [show F (T σ) = 0 from Set.indicator_of_notMem (fun hh => hs (hmem.mp hh)) _,
        Set.indicator_of_notMem hs]

/-- Deterministic transport of the literal band under an isometry. A small
spatial displacement of the isometry yields the pressure modulus used in
Subag's center-net argument. -/
private theorem pressure_transport_of_isometry {N k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β q : ℝ} (hβ : 0 ≤ β) (hq : q ∈ Icc (0 : ℝ) 1)
    (δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m m' : Vector N)
    (hm : ‖m‖ ^ 2 = (N : ℝ) * q) (hm' : ‖m'‖ ^ 2 = (N : ℝ) * q)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (hUm : U m = m')
    {B : ℝ} (hB : 0 ≤ B)
    (hU : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖U x - x‖ ≤ B * ‖m - m'‖) :
    |replicatedBandPressure k μ β q δ ρ J m -
      replicatedBandPressure k μ β q δ ρ J m'| ≤
        β * physicalBallLipschitzConstant (mixtureCoefficients μ) J *
          (B + 1) * ‖m - m'‖ / (N : ℝ) := by
  let H := field (mixtureCoefficients μ) J
  let Lip := physicalBallLipschitzConstant (mixtureCoefficients μ) J
  have hLip : 0 ≤ Lip := physicalBallLipschitzConstant_nonneg _ J
  by_cases hk : k = 0
  · subst k
    simp only [replicatedBandPressure, Nat.cast_zero, mul_zero, div_zero, sub_self, abs_zero]
    positivity
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hball (x : Vector N) (hx : ‖x‖ ^ 2 ≤ (N : ℝ)) :
      x ∈ closedBall 0 (Real.sqrt (N : ℝ)) := by
    rw [mem_closedBall, dist_zero_right]
    nlinarith [Real.sq_sqrt hNr.le, Real.sqrt_nonneg (N : ℝ), norm_nonneg x]
  have hcenterSize : (N : ℝ) * q ≤ (N : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq.2 hNr.le
  have hmBall : m ∈ closedBall 0 (Real.sqrt (N : ℝ)) :=
    hball m (hm.trans_le hcenterSize)
  have hm'Ball : m' ∈ closedBall 0 (Real.sqrt (N : ℝ)) :=
    hball m' (hm'.trans_le hcenterSize)
  have hfield (x y : Vector N)
      (hx : x ∈ closedBall 0 (Real.sqrt (N : ℝ)))
      (hy : y ∈ closedBall 0 (Real.sqrt (N : ℝ))) :
      |H x - H y| ≤ Lip * ‖x - y‖ := by
    have hh := (ball_field_lipschitz (mixtureCoefficients μ) J).dist_le_mul x hx y hy
    rw [Real.dist_eq, dist_eq_norm] at hh
    change |H x - H y| ≤ Lip * ‖x - y‖ at hh
    exact hh
  have hcenter : |H m' - H m| ≤ Lip * ‖m - m'‖ := by
    simpa only [norm_sub_rev] using hfield m' m hm'Ball hmBall
  let ν := (Measure.pi (fun _ : Fin k => sphereLaw N)).restrict (ReplicatedBand k q δ ρ m)
  let f (σ : Fin k → Vector N) := β * ∑ i : Fin k, (H (σ i) - H m)
  let g (σ : Fin k → Vector N) := β * ∑ i : Fin k, (H (U (σ i)) - H m')
  let D := β * (k : ℝ) * Lip * (B + 1) * ‖m - m'‖
  have hf : Integrable (fun σ => Real.exp (f σ)) ν :=
    (tuple_exp_integrable hN β H (field_contDiff _ J).continuous m).restrict
  have hg : Integrable (fun σ => Real.exp (g σ)) ν := by
    have hh := (tuple_exp_integrable (k := k) hN β (H ∘ U)
      ((field_contDiff _ J).continuous.comp U.continuous) m).restrict
        (s := ReplicatedBand k q δ ρ m)
    simpa only [Function.comp_apply, hUm] using hh
  have ha : ∀ᵐ σ ∂Measure.pi (fun _ : Fin k => sphereLaw N),
      ∀ i : Fin k, ‖σ i‖ ^ 2 = (N : ℝ) :=
    eventually_all.mpr fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin k => sphereLaw N) (i := i)).eventually (sphereLaw_support hN)
  have hfg : ∀ᵐ σ ∂ν, |f σ - g σ| ≤ D := by
    filter_upwards [ha.filter_mono ae_restrict_le] with σ hσ
    have hterm (i : Fin k) : |(H (σ i) - H m) - (H (U (σ i)) - H m')| ≤
        Lip * (B + 1) * ‖m - m'‖ := by
      have hxi := hball (σ i) (hσ i).le
      have hUxi := hball (U (σ i)) (by simpa only [U.norm_map] using (hσ i).le)
      have hspatial : |H (U (σ i)) - H (σ i)| ≤ Lip * (B * ‖m - m'‖) :=
        (hfield (U (σ i)) (σ i) hUxi hxi).trans
          (mul_le_mul_of_nonneg_left (hU (σ i) (hσ i)) hLip)
      calc
        _ = |(H (σ i) - H (U (σ i))) + (H m' - H m)| := by congr 1; ring
        _ ≤ |H (σ i) - H (U (σ i))| + |H m' - H m| := abs_add_le _ _
        _ ≤ Lip * (B * ‖m - m'‖) + Lip * ‖m - m'‖ := by
          rw [abs_sub_comm] at hspatial
          exact add_le_add hspatial hcenter
        _ = _ := by ring
    dsimp [f, g, D]
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hβ]
    calc
      _ ≤ β * ∑ i : Fin k, |(H (σ i) - H m) - (H (U (σ i)) - H m')| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hβ
      _ ≤ β * ∑ _i : Fin k, Lip * (B + 1) * ‖m - m'‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) hβ
      _ = _ := by simp; ring
  have hlog : |Real.log (replicatedBandPartition k μ β q δ ρ J m) -
      Real.log (replicatedBandPartition k μ β q δ ρ J m')| ≤ D := by
    rw [replicatedBandPartition_transport μ β q δ ρ J m m' U hUm]
    exact abs_log_integral_exp_sub_le ν f g (by dsimp [D]; positivity) hf hg hfg
  rw [replicatedBandPressure, replicatedBandPressure, ← sub_div, abs_div,
    abs_of_pos (mul_pos hNr hkr)]
  calc
    _ ≤ D / ((N : ℝ) * (k : ℝ)) :=
      div_le_div_of_nonneg_right hlog (mul_pos hNr hkr).le
    _ = _ := by dsimp [D, Lip]; field_simp

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof
open Set SphericalModel LiteratureSubagPhysicalDefinitions LiteratureSubagProposition24
open SourceMixedBandsLiteral.BallLipschitz
set_option autoImplicit false

/-- The center modulus in Subag's Section 3 follows from orthogonal
transport of the actual replicated integral and the ball derivative bound. -/
private theorem replicatedPressureRotationEstimate (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) :
    ReplicatedPressureRotationEstimate μ β q := by
  by_cases hqzero : q = 0
  · subst q
    refine ⟨1, by norm_num, ?_⟩
    intro N _hN J k δ ρ m m' hm hm'
    have hmzero : m = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg m])
    have hm'zero : m' = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg m'])
    simp [hmzero, hm'zero]
  have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hqzero)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
  let B : ℝ := 16 / Real.sqrt q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨β * (B + 1), mul_pos hβ (by linarith), ?_⟩
  intro N hN J k δ ρ m m' hm hm'
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hrootN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hmnorm : ‖m‖ = Real.sqrt (N : ℝ) * Real.sqrt q := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hNr.le, Real.sq_sqrt hq.1]
    exact hm
  have hnorm : ‖m‖ = ‖m'‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hm.trans hm'.symm)
  have hmne : m ≠ 0 := norm_pos_iff.mp (by rw [hmnorm]; positivity)
  obtain ⟨U, hUm, hU⟩ := exists_small_displacement_center_isometry m m' hmne hnorm
  have hdisp (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
      ‖U x - x‖ ≤ B * ‖m - m'‖ := by
    have hxnorm : ‖x‖ = Real.sqrt (N : ℝ) := by
      rw [← hx, Real.sqrt_sq (norm_nonneg _)]
    calc
      _ ≤ 16 * ‖x‖ * ‖m - m'‖ / ‖m‖ := hU x
      _ = _ := by
        rw [hxnorm, hmnorm]
        dsimp [B]
        field_simp
  have hh := pressure_transport_of_isometry (k := k) (by omega : 1 ≤ N) μ hβ.le
    ⟨hq.1, hq.2.le⟩ δ ρ J m m' hm hm' U hUm hB hdisp
  exact hh.trans_eq (by ring)

/-- Subag, Proposition 24, equation (3.1), for the original finite-mixture
model. All concentration, rotation and net inputs are proved in this file. -/
theorem proposition24 (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) :
    Proposition24 μ β q :=
  proposition24_reduced μ hβ hq (replicatedPressureRotationEstimate μ hβ hq)

end SlowEquilibration.LiteratureSubagProposition24Proof

namespace SlowEquilibration.LiteratureSubagProposition24Proof
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceReductionConsumerAsymptotic SphericalOrthogonalHaar
open SphericalRotationCovariance SphericalReversibility SphericalDynamics
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v

/-- The original downstream conclusion with Proposition 24 discharged
by the physical concentration theorem, retaining the other original inputs. -/
theorem finiteMixture_main_condensed_and_initial_literal_reduced
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  exact SourceFiniteMixtureMainLiteral.finiteMixture_main_condensed_and_initial_literal
    μ h hChen hChenSen h5 h25
    (proposition24 μ h.beta_pos ⟨h.overlap_range.1.le, h.overlap_range.2⟩)

/-- The original downstream conclusion with Proposition 24 discharged
by the physical concentration theorem, retaining the other original inputs. -/
theorem finiteMixture_all_initial_spherical_of_literature_reduced
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SourceMixedCountCapturePackage.SphericalInitialConclusions.{u,v} μ β γ := by
  exact SourceMixedCountCapturePackage.finiteMixture_all_initial_spherical_of_literature.{u,v}
    μ h hChen hChenSen h5 h25
    (proposition24 μ h.beta_pos ⟨h.overlap_range.1.le, h.overlap_range.2⟩)

end SlowEquilibration.LiteratureSubagProposition24Proof
