-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinInterpolation
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! # Actual finite-product Gaussian Gibbs replicas

Finite replica expectations are literal integrals under independent Gibbs
samples. Their Gaussian derivatives and integration by parts are derived from
the already proved nonatomic-spin integral calculus. This is a primitive for
the perturbative Ghirlanda--Guerra argument, not a positivity assumption.

Source roadmap: Panchenko, *A note on Talagrand's positivity principle*,
arXiv:0708.2453v1, proof of Theorem 2.
-/

namespace SlowEquilibration.GaussianReplicaCalculus
noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators RealInnerProductSpace
open GaussianSpinInterpolation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

variable {V H : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

/-- The actual finite product of the base spin probability. -/
def replicaBase (ν : Measure V) (n : ℕ) : Measure (Fin n → V) :=
  Measure.pi (fun _ => ν)

instance replicaBase_probability (ν : Measure V) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (replicaBase ν n) := by unfold replicaBase; infer_instance

/-- The sum of the Gaussian linear fields on genuine replicas. -/
def replicaLinear (L : V → H →L[ℝ] ℝ) (n : ℕ) (σ : Fin n → V) : H →L[ℝ] ℝ :=
  ∑ j, L (σ j)

theorem replicaLinear_measurable (L : V → H →L[ℝ] ℝ) (hL : Measurable L) (n : ℕ) :
    Measurable (replicaLinear L n) := by
  unfold replicaLinear
  exact Finset.measurable_sum _ fun j _ => hL.comp (measurable_pi_apply j)

theorem replicaLinear_bound (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) :
    ∀ᵐ σ ∂replicaBase ν n, ‖replicaLinear L n σ‖ ≤ (n : ℝ)*K := by
  have hall : ∀ᵐ σ ∂replicaBase ν n, ∀ j : Fin n, ‖L (σ j)‖ ≤ K := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_eval (μ := fun _ : Fin n => ν) j).quasiMeasurePreserving.ae hb
  filter_upwards [hall] with σ hσ
  calc
    _ ≤ ∑ j : Fin n, ‖L (σ j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, K := Finset.sum_le_sum fun j _ => hσ j
    _ = _ := by simp

/-- The normalization of the literal joint Gibbs field is Z raised to the
number of independent replicas. -/
theorem replica_moment_one (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (n : ℕ) (w : H) :
    moment (replicaBase ν n) (fun _ => 1) (replicaLinear L n) w =
      (moment ν (fun _ => 1) L w)^n := by
  unfold moment weight replicaBase
  simp only [one_mul]
  have heq : (fun σ : Fin n → V => Real.exp (replicaLinear L n σ w)) =
      (fun σ => ∏ j : Fin n, Real.exp (L (σ j) w)) := by
    funext σ
    simp only [replicaLinear,sum_apply,Real.exp_sum]
  rw [heq]
  simpa only [Fintype.card_fin] using integral_fintype_prod_eq_pow
    (ι := Fin n) (μ := ν) (fun v => Real.exp (L v w))

/-- Products of single-spin tests factor under the actual joint Gaussian
Gibbs integral. -/
theorem replica_expectation_prod (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (n : ℕ) (w : H) (f : Fin n → V → ℝ) :
    expectation (replicaBase ν n) (fun σ => ∏ j, f j (σ j)) (replicaLinear L n) w =
      ∏ j, expectation ν (f j) L w := by
  unfold expectation
  rw [replica_moment_one]
  have hmoment : moment (replicaBase ν n) (fun σ => ∏ j, f j (σ j))
      (replicaLinear L n) w = ∏ j : Fin n, moment ν (f j) L w := by
    unfold moment weight replicaBase
    have heq : (fun σ : Fin n → V => (∏ j, f j (σ j))*
        Real.exp (replicaLinear L n σ w)) =
        (fun σ => ∏ j : Fin n, f j (σ j)*Real.exp (L (σ j) w)) := by
      funext σ
      simp only [replicaLinear,sum_apply,Real.exp_sum,
        Finset.prod_mul_distrib]
    rw [heq]
    exact integral_fintype_prod_eq_prod
      (μ := fun _ : Fin n => ν) (fun j v => f j v*Real.exp (L v w))
  rw [hmoment,Finset.prod_div_distrib]
  simp

/-- The joint integral Gibbs law equals the genuine independent product
of the one-spin Gibbs probability laws. -/
theorem replica_gibbsMeasure_eq_pi (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (_hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) (w : H) :
    gibbsMeasure (replicaBase ν n) (replicaLinear L n) w =
      Measure.pi (fun _ : Fin n => gibbsMeasure ν L w) := by
  classical
  let G := gibbsMeasure ν L w
  have : IsProbabilityMeasure G := gibbsMeasure_probability ν L hL hb w
  have hLn := replicaLinear_measurable L hL n
  have hbn := replicaLinear_bound ν L hb n
  let R := gibbsMeasure (replicaBase ν n) (replicaLinear L n) w
  have : IsProbabilityMeasure R := gibbsMeasure_probability (replicaBase ν n)
    (replicaLinear L n) hLn hbn w
  change R = Measure.pi (fun _ : Fin n => G)
  symm
  apply Measure.pi_eq
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_lt_top (fun j _ => measure_lt_top G (s j))).ne).mp
  have hrect : (univ.pi s).indicator (fun _ : Fin n → V => (1 : ℝ)) =
      fun σ => ∏ j : Fin n, (s j).indicator (fun _ => (1 : ℝ)) (σ j) := by
    funext σ
    by_cases hσ : σ ∈ univ.pi s
    · have hall : ∀ j, σ j ∈ s j := by simpa only [mem_pi,mem_univ,true_implies] using hσ
      simp only [Set.indicator_of_mem hσ]
      simp only [Set.indicator_of_mem (hall _),Finset.prod_const_one]
    · have hex : ∃ j, σ j ∉ s j := by simpa only [mem_pi,mem_univ,true_implies,not_forall] using hσ
      obtain ⟨j,hj⟩ := hex
      rw [Set.indicator_of_notMem hσ]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)
  change R.real (univ.pi s) = (∏ j, G (s j)).toReal
  rw [← integral_indicator_one (MeasurableSet.univ_pi hs)]
  change (∫ σ, (univ.pi s).indicator (fun _ : Fin n → V => (1 : ℝ)) σ ∂R) = _
  rw [hrect]
  rw [show R=gibbsMeasure (replicaBase ν n) (replicaLinear L n) w from rfl,
    integral_gibbsMeasure (replicaBase ν n) (replicaLinear L n) hLn hbn,
    replica_expectation_prod]
  rw [ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [← integral_gibbsMeasure ν L hL hb]
  change (∫ v, (s j).indicator 1 v ∂G) = G.real (s j)
  exact integral_indicator_one (hs j)

/-- Literal independent Gibbs-replica expectation. -/
def replicaExpectation (ν : Measure V) (L : V → H →L[ℝ] ℝ)
    (n : ℕ) (f : (Fin n → V) → ℝ) (w : H) : ℝ :=
  ∫ σ, f σ ∂Measure.pi (fun _ : Fin n => gibbsMeasure ν L w)

theorem replicaExpectation_eq_joint (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (n : ℕ) (f : (Fin n → V) → ℝ) (w : H) :
    replicaExpectation ν L n f w =
      expectation (replicaBase ν n) f (replicaLinear L n) w := by
  rw [replicaExpectation,← replica_gibbsMeasure_eq_pi ν L hL hK hb n w]
  exact integral_gibbsMeasure (replicaBase ν n) (replicaLinear L n)
    (replicaLinear_measurable L hL n) (replicaLinear_bound ν L hb n) w f

/-- Bounded replica observables remain bounded after genuine Gibbs
normalization, uniformly in the Gaussian disorder. -/
theorem norm_replicaExpectation_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (w : H) :
    ‖replicaExpectation ν L n f w‖ ≤ C := by
  rw [replicaExpectation_eq_joint ν L hL hK hb]
  exact norm_expectation_le (replicaBase ν n) f (replicaLinear L n) hf
    (replicaLinear_measurable L hL n) hC
    (hfb.and (replicaLinear_bound ν L hb n)) w

/-- Actual finite-replica expectations are continuously differentiable
under the proved uniform observable and feature bounds. -/
theorem replicaExpectation_contDiff (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) :
    ContDiff ℝ 1 (replicaExpectation ν L n f) := by
  have heq : replicaExpectation ν L n f =
      expectation (replicaBase ν n) f (replicaLinear L n) :=
    funext (replicaExpectation_eq_joint ν L hL hK hb n f)
  rw [heq]
  exact expectation_contDiff (replicaBase ν n) f (replicaLinear L n) hf
    (replicaLinear_measurable L hL n) hC (mul_nonneg (Nat.cast_nonneg _) hK)
    (hfb.and (replicaLinear_bound ν L hb n))

theorem replicaExpectation_hasFDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (w : H) :
    HasFDerivAt (replicaExpectation ν L n f)
      (expectationDerivative (replicaBase ν n) f (replicaLinear L n) w) w := by
  have heq : replicaExpectation ν L n f =
      expectation (replicaBase ν n) f (replicaLinear L n) :=
    funext (replicaExpectation_eq_joint ν L hL hK hb n f)
  rw [heq]
  exact expectation_hasFDerivAt (replicaBase ν n) f (replicaLinear L n) hf
    (replicaLinear_measurable L hL n) hC (mul_nonneg (Nat.cast_nonneg _) hK)
    (hfb.and (replicaLinear_bound ν L hb n)) w

/-- The bounded true replica expectations are Gaussian integrable. -/
theorem replicaExpectation_gaussian_integrable {ι : Type*} [Fintype ι]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) :
    Integrable (replicaExpectation ν L n f) (SYK.standardGaussianMeasureOnEuclidean ι) :=
  Integrable.of_bound (replicaExpectation_contDiff ν L hL hK hC hb n f hf hfb).continuous.aestronglyMeasurable
    C (.of_forall (norm_replicaExpectation_le ν L hL hK hC hb n f hf hfb))

/-- Genuine finite-replica Gaussian IBP; both sides use the actual product
Gibbs law, not an assumed replica differentiation rule. -/
theorem replicaExpectation_gaussian_ibp {ι : Type*} [Fintype ι]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f)
    (hfb : ∀ᵐ σ ∂replicaBase ν n, |f σ| ≤ C) (d : EuclideanSpace ℝ ι) :
    (∫ w, inner ℝ d w * replicaExpectation ν L n f w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) =
    ∫ w, replicaExpectation ν L n
      (fun σ => f σ*replicaLinear L n σ d) w -
      replicaExpectation ν L n f w *
        replicaExpectation ν L n (fun σ => replicaLinear L n σ d) w
      ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  simp_rw [replicaExpectation_eq_joint ν L hL hK hb]
  have hbn := replicaLinear_bound ν L hb n
  have hbound : ∀ᵐ σ ∂replicaBase ν n,
      |f σ| ≤ C ∧ ‖replicaLinear L n σ‖ ≤ (n : ℝ)*K := hfb.and hbn
  rw [gaussian_expectation_ibp (replicaBase ν n) f (replicaLinear L n) hf
    (replicaLinear_measurable L hL n) hC (mul_nonneg (Nat.cast_nonneg _) hK) hbound d]
  apply integral_congr_ae
  exact .of_forall fun w => expectationDerivative_apply (replicaBase ν n) f
    (replicaLinear L n) hf (replicaLinear_measurable L hL n) hbound w d

end
end SlowEquilibration.GaussianReplicaCalculus
