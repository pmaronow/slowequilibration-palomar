-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1DriftStability
public import SlowEquilibration.SphericalC1FiniteBridge
public import SlowEquilibration.SphericalInfiniteSDEStationarity
public import SphericalAging.CompactObservableGradient

/-! Physical Gibbs stationarity transfers from actual finite ordered-tensor
Hamiltonians to a smooth Hamiltonian through field and gradient convergence.
The transition on the limit side is the genuine common-Brownian C¹ Picard
diffusion. No stationarity or operator identification is assumed. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalSmoothTensorStationarity
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalForm SphericalReversibility
open SphericalAging SphericalAging.HardSphereDynamics
open scoped Topology NNReal RealInnerProductSpace
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def smoothGradient (H : Vector N → ℝ) (_hH : ContDiff ℝ 2 H) : Vector N → Vector N :=
  gradient H

theorem smoothGradient_contDiff (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (smoothGradient H hH) :=
  CompactObservableGradient.gradient_contDiff_one hH

def smoothExpectation (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) (β : ℝ)
    (t : ℝ≥0) (f : Vector N → ℝ) : Vector N → ℝ :=
  SphericalC1Dynamics.expectation β (smoothGradient H hH) (smoothGradient_contDiff H hH) t f

def smoothTransitionKernel (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) (β : ℝ)
    (t : ℝ≥0) : Kernel (Vector N) (Vector N) :=
  SphericalC1Dynamics.transitionKernel β (smoothGradient H hH) (smoothGradient_contDiff H hH) t

instance smoothTransitionKernel_markov (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H)
    (β : ℝ) (t : ℝ≥0) : IsMarkovKernel (smoothTransitionKernel H hH β t) := by
  unfold smoothTransitionKernel
  infer_instance

theorem drift_difference_norm_le (hN : N ≠ 0) (β : ℝ) (g c : Vector N → Vector N)
    (δ : ℝ) (hgrad : ∀ z, OnSphere z → ‖c z-g z‖ ≤ δ)
    (z : Vector N) (hz : OnSphere z) :
    ‖drift β c z-drift β g z‖ ≤ |β| * δ := by
  have he : drift β c z-drift β g z = β • tangentProjection z (c z-g z) := by
    simp only [drift,SphericalForm.tangentProjection_apply,projection,inner_sub_right,
      sub_div,sub_smul,smul_sub]
    module
  rw [he,norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
  exact ((tangentProjection z).le_opNorm _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (tangentProjection_norm_le hN z hz)).trans (hgrad z hz))

/-- Convergence of actual finite-tensor transition expectations under the
original common Brownian law, from uniform actual-gradient convergence. -/
theorem finite_expectation_tendsto (hN : 1 ≤ N) (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H)
    (ν : ℕ → FiniteMixture) (J : (k : ℕ) → Disorder N (ν k).maxDegree)
    (δ : ℕ → ℝ) (hδ : ∀ k,0 ≤ δ k)
    (hgrad : ∀ k z,OnSphere z → ‖gradient (fieldOfMixture (ν k) (J k)) z-gradient H z‖ ≤ δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (β : ℝ) (x : Vector N) (hx : OnSphere x)
    (t : ℝ≥0) (f : Vector N → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ z,‖f z‖ ≤ C) :
    Tendsto (fun k => mixedExpectation (ν k) (J k) β t f x) atTop
      (𝓝 (smoothExpectation H hH β t f x)) := by
  have ht := SphericalC1Dynamics.expectation_tendsto_of_drift (by omega) β
    (smoothGradient H hH) (smoothGradient_contDiff H hH)
    (fun k => mixedGradient (ν k) (J k))
    (fun k => (mixedGradient_contDiff (ν k) (J k)).of_le (by simp))
    (fun k => |β| * δ k) (fun k => mul_nonneg (abs_nonneg β) (hδ k))
    (fun k z hz => drift_difference_norm_le (by omega) β _ _ (δ k) (hgrad k) z hz)
    (by simpa only [mul_zero] using hlim.const_mul |β|) x hx t f hf C hC
  change Tendsto (fun k => SphericalC1Dynamics.expectation β (mixedGradient (ν k) (J k))
    ((mixedGradient_contDiff (ν k) (J k)).of_le (by simp)) t f x) atTop
      (𝓝 (smoothExpectation H hH β t f x)) at ht
  simpa only [SphericalC1Dynamics.expectation_eq_mixed (by omega) _ _ β x hx t f] using ht

/-- The weighted Gibbs numerator converges in the original sphere law.
The field bound concerns the actual finite tensor approximants. -/
theorem weighted_finite_integral_tendsto (hN : 1 ≤ N) (H : Vector N → ℝ)
    (ν : ℕ → FiniteMixture) (J : (k : ℕ) → Disorder N (ν k).maxDegree)
    (M : ℝ) (hM : ∀ k x,OnSphere x → |fieldOfMixture (ν k) (J k) x| ≤ M)
    (hfield : ∀ x,OnSphere x → Tendsto (fun k => fieldOfMixture (ν k) (J k) x) atTop (𝓝 (H x)))
    (β : ℝ) (F : ℕ → Vector N → ℝ) (G : Vector N → ℝ)
    (hF : ∀ k,StronglyMeasurable (F k)) (C : ℝ≥0) (hC : ∀ k x,‖F k x‖ ≤ C)
    (hlim : ∀ x,OnSphere x → Tendsto (fun k => F k x) atTop (𝓝 (G x))) :
    Tendsto (fun k => ∫ x,Real.exp (β*fieldOfMixture (ν k) (J k) x)*F k x ∂sphereLaw N)
      atTop (𝓝 (∫ x,Real.exp (β*H x)*G x ∂sphereLaw N)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp (|β| * M)*(C : ℝ))
  · intro k
    exact (((Real.continuous_exp.comp ((fieldOfMixture_contDiff (ν k) (J k)).continuous.const_mul β)).stronglyMeasurable).mul
      (hF k)).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    filter_upwards [sphereLaw_support hN] with x hx
    have hs := (onSphere_iff_norm_sq x).mpr hx
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM k x hs) (abs_nonneg β))
    · exact hC k x
    · exact norm_nonneg _
    · exact Real.exp_nonneg _
  · filter_upwards [sphereLaw_support hN] with x hx
    have hs := (onSphere_iff_norm_sq x).mpr hx
    exact ((Real.continuous_exp.tendsto _).comp ((hfield x hs).const_mul β)).mul (hlim x hs)

/-- The genuine limit diffusion preserves its actual normalized Gibbs
law on all compact C² tests. -/
theorem compact_smoothExpectation_stationary (hN : 1 ≤ N)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H)
    (ν : ℕ → FiniteMixture) (J : (k : ℕ) → Disorder N (ν k).maxDegree)
    (M : ℝ) (hM : ∀ k x,OnSphere x → |fieldOfMixture (ν k) (J k) x| ≤ M)
    (hfield : ∀ x,OnSphere x → Tendsto (fun k => fieldOfMixture (ν k) (J k) x) atTop (𝓝 (H x)))
    (δ : ℕ → ℝ) (hδ : ∀ k,0 ≤ δ k)
    (hgrad : ∀ k z,OnSphere z → ‖gradient (fieldOfMixture (ν k) (J k)) z-gradient H z‖ ≤ δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (β : ℝ) (t : ℝ≥0)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x,smoothExpectation H hH β t f x ∂gibbsLaw N β H)=∫ x,f x ∂gibbsLaw N β H := by
  obtain ⟨C0,hC0⟩ := hfc.exists_bound_of_continuous hf.continuous
  let C : ℝ≥0 := ⟨max C0 0,le_max_right _ _⟩
  have hC : ∀ x,‖f x‖ ≤ C := fun x => (hC0 x).trans (le_max_left _ _)
  have hEm (k : ℕ) : StronglyMeasurable (mixedExpectation (ν k) (J k) β t f) := by
    have he := funext (mixedExpectation_eq_kernel (ν k) (J k) β t f hf.continuous.stronglyMeasurable)
    rw [he]
    exact hf.continuous.stronglyMeasurable.integral_kernel
  have hL := weighted_finite_integral_tendsto hN H ν J M hM hfield β
    (fun k => mixedExpectation (ν k) (J k) β t f) (smoothExpectation H hH β t f)
    hEm
    C (fun k x => by
      rw [mixedExpectation_eq_actual]
      simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
        (μ := VectorBrownian.law N) (.of_forall (fun ω => hC (mixedProcess (ν k) (J k) β x t ω))))
    (fun x hx => finite_expectation_tendsto hN H hH ν J δ hδ hgrad hlim β x hx t f hf.continuous C hC)
  have hR := weighted_finite_integral_tendsto hN H ν J M hM hfield β
    (fun _ => f) f (fun _ => hf.continuous.stronglyMeasurable) C (fun _ => hC) (fun _ _ => tendsto_const_nhds)
  have he (k : ℕ) :
      (∫ x,Real.exp (β*fieldOfMixture (ν k) (J k) x)*mixedExpectation (ν k) (J k) β t f x ∂sphereLaw N)=
        ∫ x,Real.exp (β*fieldOfMixture (ν k) (J k) x)*f x ∂sphereLaw N := by
    rw [← SphericalInfiniteModel.partition_mul_integral_gibbs hN β _
      (fieldOfMixture_contDiff (ν k) (J k)).continuous,
      ← SphericalInfiniteModel.partition_mul_integral_gibbs hN β _
      (fieldOfMixture_contDiff (ν k) (J k)).continuous]
    exact congrArg (fun z => partition N β (fieldOfMixture (ν k) (J k))*z)
      (compact_mixedExpectation_stationary hN (ν k) (J k) β hf hfc t)
  have hw := tendsto_nhds_unique (hL.congr' (.of_forall he)) hR
  apply mul_left_cancel₀ (partition_pos hN β hH.continuous).ne'
  rw [SphericalInfiniteModel.partition_mul_integral_gibbs hN β _ hH.continuous,
    SphericalInfiniteModel.partition_mul_integral_gibbs hN β _ hH.continuous]
  exact hw

def smoothGibbsWaitingLaw (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H)
    (β : ℝ) (t : ℝ≥0) : Measure (Vector N) :=
  smoothTransitionKernel H hH β t ∘ₘ gibbsLaw N β H

theorem smoothGibbsWaitingLaw_probability (hN : 1 ≤ N) (H : Vector N → ℝ)
    (hH : ContDiff ℝ 2 H) (β : ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (smoothGibbsWaitingLaw H hH β t) := by
  let := gibbsLaw_probability hN β hH.continuous
  unfold smoothGibbsWaitingLaw
  infer_instance

theorem smoothGibbsWaitingLaw_onSphere (hN : 1 ≤ N) (H : Vector N → ℝ)
    (hH : ContDiff ℝ 2 H) (β : ℝ) (t : ℝ≥0) :
    ∀ᵐ x ∂smoothGibbsWaitingLaw H hH β t,OnSphere x := by
  apply Measure.ae_comp_of_ae_ae (sphere_measurableSet N)
  filter_upwards [gibbsLaw_support hN β H] with x hx
  rw [smoothTransitionKernel,SphericalC1Dynamics.transitionKernel_apply,
    SphericalC1Dynamics.transitionLaw]
  exact (ae_map_iff (SphericalC1Dynamics.process_measurable β _ _ x t).aemeasurable
    (sphere_measurableSet N)).2
    ((SphericalC1Dynamics.process_onSphere (by omega) β _ _ x
      ((onSphere_iff_norm_sq x).mpr hx)).mono (fun _ h => h t))

theorem smoothGibbsWaitingLaw_integral (hN : 1 ≤ N) (H : Vector N → ℝ)
    (hH : ContDiff ℝ 2 H) (β : ℝ) (t : ℝ≥0)
    (f : Vector N → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ y,f y ∂smoothGibbsWaitingLaw H hH β t)=
      ∫ x,smoothExpectation H hH β t f x ∂gibbsLaw N β H := by
  let := gibbsLaw_probability hN β hH.continuous
  let := smoothGibbsWaitingLaw_probability hN H hH β t
  have hi : Integrable f (smoothGibbsWaitingLaw H hH β t) :=
    hf.integrable_of_hasCompactSupport hfc
  rw [smoothGibbsWaitingLaw,Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi,Kernel.const_apply]
  apply integral_congr_ae
  exact .of_forall (fun x => (SphericalC1Dynamics.expectation_eq_kernel β _ _ t f
    hf.stronglyMeasurable x).symm)

/-- Actual physical Gibbs stationarity follows from actual tensor C¹
approximants. This theorem can consume nonpolynomial smooth cutoffs once
their concrete approximating tensors have been constructed. -/
theorem smoothTransitionKernel_gibbs_invariant (hN : 1 ≤ N)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H)
    (ν : ℕ → FiniteMixture) (J : (k : ℕ) → Disorder N (ν k).maxDegree)
    (M : ℝ) (hM : ∀ k x,OnSphere x → |fieldOfMixture (ν k) (J k) x| ≤ M)
    (hfield : ∀ x,OnSphere x → Tendsto (fun k => fieldOfMixture (ν k) (J k) x) atTop (𝓝 (H x)))
    (δ : ℕ → ℝ) (hδ : ∀ k,0 ≤ δ k)
    (hgrad : ∀ k z,OnSphere z → ‖gradient (fieldOfMixture (ν k) (J k)) z-gradient H z‖ ≤ δ k)
    (hlim : Tendsto δ atTop (𝓝 0)) (β : ℝ) (t : ℝ≥0) :
    smoothTransitionKernel H hH β t ∘ₘ gibbsLaw N β H=gibbsLaw N β H := by
  let := gibbsLaw_probability hN β hH.continuous
  let := smoothGibbsWaitingLaw_probability hN H hH β t
  change smoothGibbsWaitingLaw H hH β t=_
  apply SphereSmoothTestMeasureExt.measure_eq_of_compactC2_integrals
    (smoothGibbsWaitingLaw_onSphere hN H hH β t)
    ((gibbsLaw_support hN β H).mono (fun x hx => (onSphere_iff_norm_sq x).mpr hx))
  intro f hf hfc
  rw [smoothGibbsWaitingLaw_integral hN H hH β t f hf.continuous hfc]
  exact compact_smoothExpectation_stationary hN H hH ν J M hM hfield δ hδ hgrad hlim β t f hf hfc

end SlowEquilibration.SphericalSmoothTensorStationarity
