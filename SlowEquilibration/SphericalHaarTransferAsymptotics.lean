module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalHaarTransfer

@[expose] public section

/-! # The probability-convergence clauses of the actual Haar transfer

Dimension-dependent disorder laws are used literally. Uniform separation
in these laws implies separation uniformly over prescribed initial
probabilities, and for initial probabilities sampled independently of the
field. The bounded-deficit expectation estimate is proved here.
-/
namespace SlowEquilibration.SphericalOrthogonalHaar
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 1800000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal

def uniformMeanDeficit (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0) (N : ℕ) : ℝ :=
  ∫ J, 1-distance μ β (T N) J (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree

/-- Literal convergence in probability with the varying-dimensional
tensor disorder law. -/
def uniformSeparationInProbability (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun N => (disorderLaw N μ.maxDegree).real
      {J | ε ≤ ‖intervalDistance μ β (T N) J (uniformInitialProbability N)-1‖})
    atTop (𝓝 0)

lemma uniformMeanDeficit_nonneg {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0) :
    0 ≤ uniformMeanDeficit μ β T N := by
  apply integral_nonneg
  intro J
  exact sub_nonneg.mpr (distance_le_one hN μ β (T N) J _)

/-- The elementary bounded-deficit estimate used in the manuscript,
proved for the actual diffusion and actual disorder measure. -/
lemma uniformMeanDeficit_le_tail {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0) {δ : ℝ} (hδ : 0 ≤ δ) :
    uniformMeanDeficit μ β T N ≤ δ+(disorderLaw N μ.maxDegree).real
      {J | δ ≤ ‖intervalDistance μ β (T N) J (uniformInitialProbability N)-1‖} := by
  let Y : Disorder N μ.maxDegree → ℝ :=
    fun J => 1-distance μ β (T N) J (uniformInitialProbability N)
  let A : Set (Disorder N μ.maxDegree) := {J | δ ≤ Y J}
  have hmY : Measurable Y := measurable_const.sub
    (distance_field_measurable hN μ β (T N) _)
  have hA : MeasurableSet A := measurableSet_le measurable_const hmY
  have hiY : Integrable Y (disorderLaw N μ.maxDegree) :=
    (integrable_const (1:ℝ)).sub (distance_integrable hN μ β (T N) _)
  have hiA : Integrable (A.indicator (fun _ => (1:ℝ))) (disorderLaw N μ.maxDegree) :=
    (integrable_const (1:ℝ)).indicator hA
  have hb : ∀ J, Y J ≤ δ+A.indicator (fun _ => (1:ℝ)) J := by
    intro J
    by_cases hJ : J ∈ A
    · rw [indicator_of_mem hJ]
      have hy := distance_nonneg hN μ β (T N) J (uniformInitialProbability N)
      dsimp [Y]
      linarith
    · rw [indicator_of_notMem hJ]
      have hj : Y J < δ := lt_of_not_ge hJ
      simpa only [add_zero] using hj.le
  have hint := integral_mono hiY ((integrable_const δ).add hiA) hb
  change (∫ J, Y J ∂disorderLaw N μ.maxDegree) ≤
    ∫ J, δ+A.indicator (fun _ => (1:ℝ)) J ∂disorderLaw N μ.maxDegree at hint
  rw [integral_add (integrable_const δ) hiA,integral_const,
    integral_indicator_const 1 hA,probReal_univ,one_smul,smul_eq_mul,mul_one] at hint
  have he : A={J | δ ≤ ‖intervalDistance μ β (T N) J (uniformInitialProbability N)-1‖} := by
    ext J
    change (δ ≤ 1-distance μ β (T N) J (uniformInitialProbability N)) ↔
      δ ≤ ‖intervalDistance μ β (T N) J (uniformInitialProbability N)-1‖
    rw [intervalDistance_eq_endpoint hN μ β (T N)]
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (distance_le_one hN μ β (T N) J _))]
    rw [neg_sub]
  simpa only [uniformMeanDeficit,Y,he] using hint

/-- Bounded convergence in probability is derived, rather than supplied
as an expected-deficit hypothesis. -/
theorem uniformMeanDeficit_tendsto_zero (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (hsep : uniformSeparationInProbability μ β T) :
    Tendsto (uniformMeanDeficit μ β T) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact ha.trans_le (uniformMeanDeficit_nonneg hN μ β T)
  · intro b hb
    have ht := (tendsto_order.mp (hsep (b/2) (by positivity))).2 (b/2) (by positivity)
    filter_upwards [eventually_ge_atTop (1:ℕ),ht] with N hN htN
    have hm := uniformMeanDeficit_le_tail hN μ β T (δ := b/2) (by positivity)
    linarith

def uniformPrescribedFailure (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0) (ε : ℝ) (N : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ ν : ProbabilityMeasure (Vector N),
    (∀ᵐ x ∂ν.toMeasure, OnSphere x) ∧
    r=(disorderLaw N μ.maxDegree).real {J | intervalDistance μ β (T N) J ν < 1-ε}}

lemma uniformPrescribedFailure_nonneg {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0) (ε : ℝ) :
    0 ≤ uniformPrescribedFailure μ β T ε N := by
  let S : Set ℝ := {r | ∃ ν : ProbabilityMeasure (Vector N),
    (∀ᵐ x ∂ν.toMeasure, OnSphere x) ∧
    r=(disorderLaw N μ.maxDegree).real {J | intervalDistance μ β (T N) J ν < 1-ε}}
  have hb : BddAbove S := by
    refine ⟨1,?_⟩
    rintro r ⟨ν,hν,rfl⟩
    exact measureReal_le_one
  have hu : (disorderLaw N μ.maxDegree).real
      {J | intervalDistance μ β (T N) J (uniformInitialProbability N)<1-ε} ∈ S := by
    refine ⟨uniformInitialProbability N,?_,rfl⟩
    exact (sphereLaw_support hN).mono fun x hx => (onSphere_iff_norm_sq x).mpr hx
  exact measureReal_nonneg.trans (le_csSup hb hu)

/-- The source supremum, outside disorder probability, tends to zero
uniformly over every prescribed spherical initial probability. -/
theorem uniformPrescribedFailure_tendsto_zero (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (hsep : uniformSeparationInProbability μ β T) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (uniformPrescribedFailure μ β T ε) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact uniformPrescribedFailure_nonneg hN μ β T ε
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact uniform_prescribed_initial_failure_le hN μ β (T N) hε
  · simpa only [uniformMeanDeficit,mul_zero] using
      (uniformMeanDeficit_tendsto_zero μ β T hsep).const_mul ε⁻¹

/-- The actual independent product law gives separation for every random
initial probability supported on the sphere; singular laws are included. -/
theorem independent_random_initial_failure_tendsto_zero
    (μ : FiniteMixture) (β : ℝ) (T : ℕ → ℝ≥0)
    (hsep : uniformSeparationInProbability μ β T)
    (η : ∀ N, Measure (ProbabilityMeasure (Vector N)))
    [∀ N, IsProbabilityMeasure (η N)]
    (hη : ∀ N, 1 ≤ N → ∀ᵐ ν ∂η N, ∀ᵐ x ∂ν.toMeasure, OnSphere x)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => ((disorderLaw N μ.maxDegree).prod (η N)).real
      {p | intervalDistance μ β (T N) p.1 p.2 < 1-ε}) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact .of_forall fun N => measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact independent_random_initial_failure_le hN μ β (T N) (η N) (hη N hN) hε
  · simpa only [uniformMeanDeficit,mul_zero] using
      (uniformMeanDeficit_tendsto_zero μ β T hsep).const_mul ε⁻¹

end
end SlowEquilibration.SphericalOrthogonalHaar
