module
public import FourPapersCommon.MixedSecondInterpolationContinuity

@[expose] public section

/-! Genuine mixed second-interpolation derivative and endpoint bounds with
actual theta corrections and normalized split-replica laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 theorem section5Rho_mem_unit (s : RSBScheme k) {r : ℕ} (hr : r≤k+2)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) {p : ℕ} (hp : p≤k+3) :
    section5Rho s r u p∈Icc (-1:ℝ) 1 := by
  unfold section5Rho
  split_ifs with hpr hpr
  · exact ⟨by linarith [s.q_nonneg (by omega : p≤k+2)],s.q_le_one (by omega)⟩
  · exact ⟨by linarith [hu.1],hu.2⟩
  · exact ⟨by linarith [s.q_nonneg (by omega : p-1≤k+2)],s.q_le_one (by omega)⟩

/-- Theorem 3.1's derivative estimate for the actual left Section 5 path. -/
theorem deriv_mixedLeftInterpolation_le
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u w : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (mixedLeftInterpolation ξ s h sk.U r m t u) w ≤
      -t * (mixedPairCascadeCorrection ξ (section5Mass s r m) (section5Rho s r u)
        (fun p=>section5Rho s r u (min p r)) (k+2)) := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  rw [(hasDerivAt_mixedLeftInterpolation_replica hn ξ s h sk hr hm0 ht hu hw).deriv]
  exact mixedAveragedReplicaPressureDerivative_le hn
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) ξ u ht.1
    (section5Mass s r m) (section5Rho s r u)
    (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w) r (k + 2)
    (section5Mass_endpoints s hr0 hr m).1 (section5Mass_endpoints s hr0 hr m).2
    (fun j => section5Mass_nonneg s hr hm0 (by omega))
    (fun j => section5InterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hu) ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5Mass_mono s hr hm (by omega))
    (section5Rho_endpoints s hr0 hr u).1 (section5Rho_endpoints s hr0 hr u).2
    (by omega) (by simp [section5Rho])
    (fun p hp=>section5Rho_mem_unit s (by omega)
      ⟨(s.q_nonneg (by omega)).trans hu.1,hu.2.trans (s.q_le_one (by omega))⟩ hp)
    (fun _ => h) (fun _ => h)

/-- Closed-interval endpoint transport: the actual estimate (5.9). -/
theorem mixedLeftInterpolation_endpoint_bound
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1) / 2) (s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      mixedLeftInterpolation ξ s h sk.U r m t u 0 -
      t * (mixedPairCascadeCorrection ξ (section5Mass s r m) (section5Rho s r u)
        (fun p=>section5Rho s r u (min p r)) (k+2)) := by
  have hm0 : 0 ≤ m := (div_nonneg (s.m_nonneg (by omega)) (by norm_num)).trans hm.1
  have hc := continuousOn_mixedLeftInterpolation ξ s h sk.hU hr hm0 ht hu
  have hd : DifferentiableOn ℝ (mixedLeftInterpolation ξ s h sk.U r m t u)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun w hw=>(hasDerivAt_mixedLeftInterpolation_replica hn ξ s h sk hr hm0 ht hu hw).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (mixedLeftInterpolation ξ s h sk.U r m t u) w ≤
        -t * (mixedPairCascadeCorrection ξ (section5Mass s r m) (section5Rho s r u)
          (fun p=>section5Rho s r u (min p r)) (k+2)) := by
    rw [interior_Icc]
    exact fun w hw => deriv_mixedLeftInterpolation_le hn ξ s h sk hr0 hr hm ht hu hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [mixedLeftInterpolation_one ξ s h sk.U hr0 hr m u ht.2] at H
  simp only [sub_zero, mul_one] at H
  linarith

/-- The dual right path satisfies the corresponding deterministic correction. -/
theorem deriv_mixedRightInterpolation_le
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u w : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (mixedRightInterpolation ξ s h sk.U r m t u) w ≤
      -t * (mixedPairCascadeCorrection ξ (section5RightMass s r m) (section5RightRho s r u)
        (fun p=>section5RightRho s r u (min p (r+1))) (k+2)) := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  rw [(hasDerivAt_mixedRightInterpolation_replica hn ξ s h sk hr hm0 ht hu hw).deriv]
  have H := mixedAveragedReplicaPressureDerivative_le hn
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) ξ u ht.1
    (section5RightMass s r m) (section5RightRho s r u)
    (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w) (r + 1) (k + 2)
    (section5RightMass_endpoints s hr0 hr m).1 (section5RightMass_endpoints s hr0 hr m).2
    (fun j => section5RightMass_nonneg s hr hm0 (by omega))
    (fun j => section5RightInterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hu) ⟨hw.1.le, hw.2.le⟩)
    (fun p hp => section5RightMass_mono s hr hm (by omega))
    (section5RightRho_endpoints s hr u).1 (section5RightRho_endpoints s hr u).2
    (by omega) (by simp [section5RightRho, section5Rho])
    (fun p hp=>section5Rho_mem_unit s (by omega)
      ⟨(s.q_nonneg (by omega)).trans hu.1,hu.2.trans (s.q_le_one (by omega))⟩ hp)
    (fun _ => h) (fun _ => h)
  simpa only [show k + 2 + 1 - (r + 1) = k + 2 - r by omega,
    show k + 2 + 1 = k + 3 by omega] using! H

/-- Endpoint transport for the dual construction, with no endpoint derivative assumption. -/
theorem mixedRightInterpolation_endpoint_bound
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k + 1) {m t u : ℝ}
    (hm : m ∈ Set.Icc (s.m (r - 1)) (2 * s.m r))
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k + 2 - r) t u ≤
      mixedRightInterpolation ξ s h sk.U r m t u 0 -
      t * (mixedPairCascadeCorrection ξ (section5RightMass s r m) (section5RightRho s r u)
        (fun p=>section5RightRho s r u (min p (r+1))) (k+2)) := by
  have hm0 : 0 ≤ m := (s.m_nonneg (by omega)).trans hm.1
  have hc := continuousOn_mixedRightInterpolation ξ s h sk.hU hr hm0 ht hu
  have hd : DifferentiableOn ℝ (mixedRightInterpolation ξ s h sk.U r m t u)
      (interior (Set.Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun w hw=>(hasDerivAt_mixedRightInterpolation_replica hn ξ s h sk hr hm0 ht hu hw).differentiableAt.differentiableWithinAt
  have hb : ∀ w ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv (mixedRightInterpolation ξ s h sk.U r m t u) w ≤
        -t * (mixedPairCascadeCorrection ξ (section5RightMass s r m) (section5RightRho s r u)
          (fun p=>section5RightRho s r u (min p (r+1))) (k+2)) := by
    rw [interior_Icc]
    exact fun w hw => deriv_mixedRightInterpolation_le hn ξ s h sk hr0 hr hm ht hu hw
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [mixedRightInterpolation_one ξ s h sk.U hr0 hr m u ht.2] at H
  simp only [sub_zero, mul_one] at H
  linarith

end FourPapersCommon
