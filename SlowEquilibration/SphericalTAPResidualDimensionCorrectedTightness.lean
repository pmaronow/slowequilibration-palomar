-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPResidualStrictStatic
public import SlowEquilibration.SphericalTAPCriticalBandPressure
public import SlowEquilibration.SphericalLatitudeRegularDisorder

@[expose] public section
/-! Genuine normalized residual partition lower tails with the physical
ambient/transverse dimension correction. Actual Gaussian tensor regularity
makes the temperature correction cost uniformly bounded; the genuine HMP
lower tail is used at one fixed, internally certified RS temperature. -/
namespace SlowEquilibration.SphericalTAPCriticalBand
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalTaylorRemainder
open SphericalTAPCertificate SphericalTAPResidualStrictStatic
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def physicalResidualNormalizedPartition (n:ℕ) (θ:FiniteMixture) (β:ℝ)
    (J:Disorder n θ.maxDegree):ℝ:=
  Real.exp (-((n+1:ℕ):ℝ)*β^2*θ.xi 1/2)*
    mixturePartition θ (dimensionCorrectedTemperature β 1 n) J

theorem physical_temperature_correction_bound {n:ℕ} (hn:1 ≤ n) {β:ℝ} (hβ:0 ≤ β) :
    0 ≤ dimensionCorrectedTemperature β 1 n-β ∧
      (dimensionCorrectedTemperature β 1 n-β)*(n:ℝ) ≤ β/2:=by
  have hnR:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  let S:=Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ))
  have hS:0 ≤ S:=Real.sqrt_nonneg _
  have hSsq:S^2=((n+1:ℕ):ℝ)/(n:ℝ):=Real.sq_sqrt (by positivity)
  have hEq:(n:ℝ)*(S^2-1)=1:=by rw [hSsq];push_cast;field_simp;ring
  have hS1:1 ≤ S:=by
    apply (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 1) (by positivity)).mpr
    norm_num only [one_pow]
    apply (le_div_iff₀ hnR).mpr
    push_cast
    linarith
  have hNon:0 ≤ (S-1)*(n:ℝ):=mul_nonneg (sub_nonneg.mpr hS1) hnR.le
  have hHalf:(S-1)*(n:ℝ) ≤ 1/2:=by
    have H:=mul_nonneg hNon (sub_nonneg.mpr hS1)
    nlinarith
  unfold dimensionCorrectedTemperature
  change 0 ≤ β*S-β ∧ (β*S-β)*(n:ℝ) ≤ β/2
  constructor
  · nlinarith [mul_nonneg hβ (sub_nonneg.mpr hS1)]
  · nlinarith [mul_le_mul_of_nonneg_left hHalf hβ]

/-- An actual regular tensor realization pays only a fixed likelihood
factor under the N/(N-1) temperature and annealed corrections. -/
theorem physicalResidualNormalizedPartition_regular_lower
    (n:ℕ) (hn:1 ≤ n) (θ:FiniteMixture) {β:ℝ} (hβ:0 ≤ β)
    (J:Disorder n θ.maxDegree) (hJ:J∈regularDisorder) :
    Real.exp (-(β*derivativeConstant (mixtureCoefficients θ)/2+β^2*θ.xi 1/2))*
      likelihood (mixtureCoefficients θ) β J ≤ physicalResidualNormalizedPartition n θ β J:=by
  let c:=mixtureCoefficients θ
  let C:=derivativeConstant c
  let s:=dimensionCorrectedTemperature β 1 n
  let F:=modelContinuousField c (fun x:CompactSphereCarrier.Carrier n=>x.val)
    continuous_subtype_val (euclideanDisorder J)
  let :IsProbabilityMeasure (CompactSphereCarrier.law n):=CompactSphereCarrier.law_probability hn
  have hC:0<C:=derivativeConstant_pos c
  have hNorm:‖F‖ ≤ C*(n:ℝ):=by
    apply (F.norm_le (by positivity)).mpr
    intro x
    rw [modelContinuousField_apply,valueObservation_actual,Real.norm_eq_abs]
    exact (field_regularDisorder_ball_bounds hn c J hJ x.val
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using x.property)).1
  have hTemp:=physical_temperature_correction_bound hn hβ
  have hL:|Real.log (mixturePartition θ s J)-Real.log (mixturePartition θ β J)| ≤ (s-β)*‖F‖:=by
    have H:=(ContinuousFieldPartition.logPartition_lipschitz (CompactSphereCarrier.law n) 1).norm_sub_le
      (s • F) (β • F)
    rw [compact_scaled_model_logPartition n hn θ 1 s J,
      compact_scaled_model_logPartition n hn θ 1 β J] at H
    rw [Real.norm_eq_abs] at H
    change |Real.log (mixturePartition θ (1*s) J)-Real.log (mixturePartition θ (1*β) J)| ≤
      |(1:ℝ)| * ‖s • F-β • F‖ at H
    simp only [one_mul,abs_one] at H
    rw [←sub_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hTemp.1] at H
    exact H
  have hLoss:(s-β)*‖F‖ ≤ β*C/2:=by
    calc
      _ ≤ (s-β)*(C*(n:ℝ)):=mul_le_mul_of_nonneg_left hNorm hTemp.1
      _ = C*((s-β)*(n:ℝ)):=by ring
      _ ≤ C*(β/2):=mul_le_mul_of_nonneg_left hTemp.2 hC.le
      _ = _:=by ring
  have hLog:Real.log (mixturePartition θ β J)-β*C/2 ≤ Real.log (mixturePartition θ s J):=by
    have H:=abs_le.mp (hL.trans hLoss)
    linarith [H.1]
  have hZ:Real.exp (-β*C/2)*mixturePartition θ β J ≤ mixturePartition θ s J:=by
    have H:=Real.exp_le_exp.mpr hLog
    rw [Real.exp_sub,Real.exp_log (mixturePartition_pos hn θ β J),
      Real.exp_log (mixturePartition_pos hn θ s J)] at H
    rw [div_eq_mul_inv,←Real.exp_neg] at H
    rw [show -(β*C/2)= -β*C/2 by ring] at H
    simpa only [mul_comm] using H
  have H:=mul_le_mul_of_nonneg_left hZ
    (Real.exp_nonneg (-((n+1:ℕ):ℝ)*β^2*θ.xi 1/2))
  unfold physicalResidualNormalizedPartition
  calc
    _=Real.exp (-((n+1:ℕ):ℝ)*β^2*θ.xi 1/2)*
        (Real.exp (-β*C/2)*mixturePartition θ β J):=by
      unfold likelihood annealedExponent
      rw [covariancePolynomial_mixture]
      change Real.exp (-(β*C/2+β^2*θ.xi 1/2))*
        (mixturePartition θ β J*Real.exp (-((n:ℝ)*β^2*θ.xi 1/2)))=_
      calc
        _=(Real.exp (-(β*C/2+β^2*θ.xi 1/2))*Real.exp (-((n:ℝ)*β^2*θ.xi 1/2)))*
          mixturePartition θ β J:=by ring
        _=(Real.exp (-((n+1:ℕ):ℝ)*β^2*θ.xi 1/2)*Real.exp (-β*C/2))*
          mixturePartition θ β J:=by
          congr 1
          rw [←Real.exp_add,←Real.exp_add]
          congr 1
          push_cast
          ring
        _=_:=by ring
    _ ≤ _:=H

/-- Actual physical residual likelihood lower-tail tightness. Its only
temperature condition is the fixed strict RS threshold; all dimensional
correction and genuine Gaussian exceptional events are proved internally. -/
theorem physicalResidualNormalizedPartition_lower_tail (θ:FiniteMixture) {β:ℝ}
    (hβ:0<β) (hStatic:β<Thresholds.staticThreshold θ.xi) :
    ∀ ε:ℝ,0<ε → ∃ τ:ℝ,∀ᶠ n:ℕ in atTop,
      (disorderLaw n θ.maxDegree).real {J|physicalResidualNormalizedPartition n θ β J<Real.exp (-τ)} ≤ ε:=by
  intro ε hε
  obtain ⟨τ,hTail⟩:=general_likelihoodLowerTailTight θ hβ hStatic (ε/2) (half_pos hε)
  let K:=β*derivativeConstant (mixtureCoefficients θ)/2+β^2*θ.xi 1/2
  have hBad:Tendsto (fun n:ℕ=>Real.exp (-(n:ℝ))) atTop (𝓝 0):=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  refine ⟨τ+K,?_⟩
  filter_upwards [hTail,eventually_ge_atTop (2:ℕ),hBad.eventually (gt_mem_nhds (half_pos hε))]
    with n hn hdim hsmall
  have hsub:{J:Disorder n θ.maxDegree|physicalResidualNormalizedPartition n θ β J<Real.exp (-(τ+K))} ⊆
      (regularDisorder (N:=n) (P:=θ.maxDegree))ᶜ ∪
        {J|likelihood (mixtureCoefficients θ) β J<Real.exp (-τ)}:=by
    intro J hJ
    by_cases hreg:J∈regularDisorder
    · apply Or.inr
      have H:=physicalResidualNormalizedPartition_regular_lower n (by omega) θ hβ.le J hreg
      have he:Real.exp (-(τ+K))=Real.exp (-K)*Real.exp (-τ):=by
        rw [←Real.exp_add]
        congr 1
        ring
      change physicalResidualNormalizedPartition n θ β J<Real.exp (-(τ+K)) at hJ
      rw [he] at hJ
      exact (mul_lt_mul_iff_right₀ (Real.exp_pos (-K))).mp (by
        simpa only [K,mul_comm] using H.trans_lt hJ)
    · exact Or.inl hreg
  exact ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
    ((add_le_add (regularDisorder_failure_probability hdim) hn).trans (by linarith))

/-- Raw source certification gives the physical residual lower tail,
without assuming residual-static, HMP or normalized tightness properties. -/
theorem certified_physicalResidualNormalizedPartition_lower_tail
    {μ:FiniteMixture} {β x Q:ℝ} (h:Certificate μ β x Q) :
    let θ:=μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)
    ∀ ε:ℝ,0<ε → ∃ τ:ℝ,∀ᶠ n:ℕ in atTop,
      (disorderLaw n θ.maxDegree).real {J|physicalResidualNormalizedPartition n θ β J<Real.exp (-τ)} ≤ ε:=
  physicalResidualNormalizedPartition_lower_tail _ h.beta_pos (certificate_residual_lt_staticThreshold h)

end
end SlowEquilibration.SphericalTAPCriticalBand
