module
public import FourPapersCommon.MixedSecondInterpolationOffDiagonal
public import FourPapersCommon.MixedSecondInterpolationBounds

@[expose] public section

/-! Actual off-diagonal mixed endpoint bounds. Physical overlap mismatch is
measured by the covariance tangent remainder. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem mixedLeftInterpolationOffDiagonal_one (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (U : Ω→EnergySpace n) {r : ℕ}
    (hr0 : 1≤r) (hr : r≤k+1) (m u v : ℝ) {t : ℝ} (ht : t≤1) :
    mixedLeftInterpolationOffDiagonal ξ s h U r m t u v 1=
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U (k+2-r) t u := by
  have he : mixedLeftInterpolationOffDiagonal ξ s h U r m t u v 1=
      mixedLeftInterpolation ξ s h U r m t u 1 := by
    simp only [mixedLeftInterpolationOffDiagonal,mixedLeftInterpolation,
      section5InterpolationVariance_one]
  rw [he,mixedLeftInterpolation_one ξ s h U hr0 hr m u ht]

 theorem mixedRightInterpolationOffDiagonal_one (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (U : Ω→EnergySpace n) {r : ℕ}
    (hr0 : 1≤r) (hr : r≤k+1) (m u v : ℝ) {t : ℝ} (ht : t≤1) :
    mixedRightInterpolationOffDiagonal ξ s h U r m t u v 1=
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U (k+2-r) t u := by
  have he : mixedRightInterpolationOffDiagonal ξ s h U r m t u v 1=
      mixedRightInterpolation ξ s h U r m t u 1 := by
    simp only [mixedRightInterpolationOffDiagonal,mixedRightInterpolation,
      section5RightInterpolationVariance_one]
  rw [he,mixedRightInterpolation_one ξ s h U hr0 hr m u ht]

 theorem mixedLeftInterpolationOffDiagonal_zero (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (U : Ω→EnergySpace n) (r : ℕ) (m t u v : ℝ) :
    mixedLeftInterpolationOffDiagonal ξ s h U r m t u v 0=
      section5FieldEndpoint n (mixedClockScheme ξ s) (mixedBeta ξ) h u r m
        (mixedLeftSplitVariance ξ s r t v) := by
  rw [mixedLeftSplitVariance_eq_clock]
  simp only [mixedLeftInterpolationOffDiagonal,zero_mul,Real.sqrt_zero,zero_smul,
    constrainedPairFieldBase_zero,section5InterpolationVariance_zero,integral_const,
    probReal_univ,smul_eq_mul,one_mul,section5FieldEndpoint,one_div]
  rfl

 theorem mixedRightInterpolationOffDiagonal_zero (ξ : AdmissibleEvenMixture)
    (s : RSBScheme k) (h : ℝ) (U : Ω→EnergySpace n) (r : ℕ) (m t u v : ℝ) :
    mixedRightInterpolationOffDiagonal ξ s h U r m t u v 0=
      section5RightFieldEndpoint n (mixedClockScheme ξ s) (mixedBeta ξ) h u r m
        (mixedRightSplitVariance ξ s r t v) := by
  rw [mixedRightSplitVariance_eq_clock]
  simp only [mixedRightInterpolationOffDiagonal,zero_mul,Real.sqrt_zero,zero_smul,
    constrainedPairFieldBase_zero,section5RightInterpolationVariance_zero,integral_const,
    probReal_univ,smul_eq_mul,one_mul,section5RightFieldEndpoint,one_div]
  rfl

/-- Theorem 3.1's derivative estimate for the actual left Section 5 path. -/
theorem deriv_mixedLeftInterpolationOffDiagonal_le
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u v w : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (mixedLeftInterpolationOffDiagonal ξ s h sk.U r m t u v) w ≤
      -t * (mixedPairCascadeCorrection ξ (section5Mass s r m) (section5Rho s r v)
        (fun p=>section5Rho s r v (min p r)) (k+2)) + t*ξ.tangentRemainder u v := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  rw [(hasDerivAt_mixedLeftInterpolationOffDiagonal_replica hn ξ s h sk (u:=u) hr hm0 ht hv hw).deriv]
  exact mixedAveragedReplicaPressureDerivative_le_mismatch hn
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) ξ u v ht.1
    (section5Mass s r m) (section5Rho s r v)
    (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w) r (k + 2)
    (section5Mass_endpoints s hr0 hr m).1 (section5Mass_endpoints s hr0 hr m).2
    (fun j => section5Mass_nonneg s hr hm0 (by omega))
    (fun j => section5InterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hv) ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5Mass_mono s hr hm (by omega))
    (section5Rho_endpoints s hr0 hr v).1 (section5Rho_endpoints s hr0 hr v).2
    (by omega) (by simp [section5Rho])
    (fun p hp=>section5Rho_mem_unit s (by omega)
      ⟨(s.q_nonneg (by omega)).trans hv.1,hv.2.trans (s.q_le_one (by omega))⟩ hp)
    (fun _ => h) (fun _ => h)

/-- Closed-interval endpoint transport: the actual estimate (5.9). -/
theorem mixedLeftInterpolationOffDiagonal_endpoint_bound
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u v : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      mixedLeftInterpolationOffDiagonal ξ s h sk.U r m t u v 0 -
      t * (mixedPairCascadeCorrection ξ (section5Mass s r m) (section5Rho s r v)
        (fun p=>section5Rho s r v (min p r)) (k+2)) + t*ξ.tangentRemainder u v := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  have hc := continuousOn_mixedLeftInterpolationOffDiagonal ξ s h sk.hU (u:=u) hr hm0 ht hv
  have hd : DifferentiableOn ℝ (mixedLeftInterpolationOffDiagonal ξ s h sk.U r m t u v)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun w hw=>(hasDerivAt_mixedLeftInterpolationOffDiagonal_replica hn ξ s h sk (u:=u) hr hm0 ht hv hw).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (mixedLeftInterpolationOffDiagonal ξ s h sk.U r m t u v) w ≤
        -t * (mixedPairCascadeCorrection ξ (section5Mass s r m) (section5Rho s r v)
          (fun p=>section5Rho s r v (min p r)) (k+2)) + t*ξ.tangentRemainder u v := by
    rw [interior_Icc]
    exact fun w hw => deriv_mixedLeftInterpolationOffDiagonal_le hn ξ s h sk (u:=u) hr0 hr hm ht hv hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [mixedLeftInterpolationOffDiagonal_one ξ s h sk.U hr0 hr m u v ht.2] at H
  simp only [sub_zero, mul_one] at H
  linarith

/-- The dual right path satisfies the corresponding deterministic correction. -/
theorem deriv_mixedRightInterpolationOffDiagonal_le
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u v w : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (mixedRightInterpolationOffDiagonal ξ s h sk.U r m t u v) w ≤
      -t * (mixedPairCascadeCorrection ξ (section5RightMass s r m) (section5RightRho s r v)
        (fun p=>section5RightRho s r v (min p (r+1))) (k+2)) + t*ξ.tangentRemainder u v := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  rw [(hasDerivAt_mixedRightInterpolationOffDiagonal_replica hn ξ s h sk (u:=u) hr hm0 ht hv hw).deriv]
  have H := mixedAveragedReplicaPressureDerivative_le_mismatch hn
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) ξ u v ht.1
    (section5RightMass s r m) (section5RightRho s r v)
    (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w) (r + 1) (k + 2)
    (section5RightMass_endpoints s hr0 hr m).1 (section5RightMass_endpoints s hr0 hr m).2
    (fun j => section5RightMass_nonneg s hr hm0 (by omega))
    (fun j => section5RightInterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hv) ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5RightMass_mono s hr hm (by omega))
    (section5RightRho_endpoints s hr v).1 (section5RightRho_endpoints s hr v).2
    (by omega) (by simp [section5RightRho, section5Rho])
    (fun p hp=>section5Rho_mem_unit s (by omega)
      ⟨(s.q_nonneg (by omega)).trans hv.1,hv.2.trans (s.q_le_one (by omega))⟩ hp)
    (fun _ => h) (fun _ => h)
  simpa only [show k + 2 + 1 - (r + 1) = k + 2 - r by omega,
    show k + 2 + 1 = k + 3 by omega] using! H

/-- Endpoint transport for the dual construction, with no endpoint derivative assumption. -/
theorem mixedRightInterpolationOffDiagonal_endpoint_bound
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u v : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      mixedRightInterpolationOffDiagonal ξ s h sk.U r m t u v 0 -
      t * (mixedPairCascadeCorrection ξ (section5RightMass s r m) (section5RightRho s r v)
        (fun p=>section5RightRho s r v (min p (r+1))) (k+2)) + t*ξ.tangentRemainder u v := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  have hc := continuousOn_mixedRightInterpolationOffDiagonal ξ s h sk.hU (u:=u) hr hm0 ht hv
  have hd : DifferentiableOn ℝ (mixedRightInterpolationOffDiagonal ξ s h sk.U r m t u v)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun w hw=>(hasDerivAt_mixedRightInterpolationOffDiagonal_replica hn ξ s h sk (u:=u) hr hm0 ht hv hw).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (mixedRightInterpolationOffDiagonal ξ s h sk.U r m t u v) w ≤
        -t * (mixedPairCascadeCorrection ξ (section5RightMass s r m) (section5RightRho s r v)
          (fun p=>section5RightRho s r v (min p (r+1))) (k+2)) + t*ξ.tangentRemainder u v := by
    rw [interior_Icc]
    exact fun w hw => deriv_mixedRightInterpolationOffDiagonal_le hn ξ s h sk (u:=u) hr0 hr hm ht hv hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [mixedRightInterpolationOffDiagonal_one ξ s h sk.U hr0 hr m u v ht.2] at H
  simp only [sub_zero, mul_one] at H
  linarith

end FourPapersCommon
