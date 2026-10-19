module
public import FourPapersCommon.MixedSecondInterpolationDerivative
public import FourPapersCommon.MixedSecondInterpolationMismatch

@[expose] public section

/-! Actual mixed second interpolation with physical constrained overlap u
independent of the physical trial overlap v. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology Set SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

 def mixedLeftInterpolationOffDiagonal (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (h : ℝ) (U : Ω→EnergySpace n) (r : ℕ) (m t u v w : ℝ) : ℝ :=
  (1/(n:ℝ))*∫ω,coupledFieldCascade n (fun j=>section5Mass s r m (k+2-j))
    (fun j=>section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t
      (ξ.clock v) r (k+2-j) w) (k+3-r)
    (constrainedPairFieldBase n (Real.sqrt (w*t) • U ω) u) (k+3)
    (fun _=>h) (fun _=>h) ∂ℙ

 def mixedRightInterpolationOffDiagonal (ξ : AdmissibleEvenMixture) (s : RSBScheme k)
    (h : ℝ) (U : Ω→EnergySpace n) (r : ℕ) (m t u v w : ℝ) : ℝ :=
  (1/(n:ℝ))*∫ω,coupledFieldCascade n (fun j=>section5RightMass s r m (k+2-j))
    (fun j=>section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t
      (ξ.clock v) r (k+2-j) w) (k+2-r)
    (constrainedPairFieldBase n (Real.sqrt (w*t) • U ω) u) (k+3)
    (fun _=>h) (fun _=>h) ∂ℙ

private theorem offdiag_sqrt_time_derivative_mul {t w : ℝ} (ht : 0 ≤ t) (hw : 0 < w) :
    t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
  by_cases hz : t = 0
  · simp [hz]
  · have hs : Real.sqrt (w * t) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hw (lt_of_le_of_ne ht (Ne.symm hz)))).ne'
    field_simp

/-- Explicit trace-plus-heat formula for the actual left pressure.
The disorder coefficient is t/2 before site normalization. -/
theorem hasDerivAt_mixedLeftInterpolationOffDiagonal_trace
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u v w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (mixedLeftInterpolationOffDiagonal ξ s h Z r m t u v)
      ((1 / (n : ℝ)) * (t / 2 * (∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond
          (fun j => section5Mass s r m (k + 2 - j))
          (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w)
          (k + 3 - r) (k + 3) (Real.sqrt (w * t) • Z ω)
          (hZ.w i) (hZ.w i) u (fun _ => h) (fun _ => h) ∂ℙ) +
        ∑ l : Fin (k + 3),
          (-(t * (mixedBeta ξ) ^ 2 * (section5Rho (mixedClockScheme ξ s) r (ξ.clock v) (k + 2 - l + 1) -
            section5Rho (mixedClockScheme ξ s) r (ξ.clock v) (k + 2 - l)))) *
          (if 0 < section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - l) w then
            ∫ ω, constrainedLevelVarianceD (Real.sqrt (w * t) • Z ω) u
              (fun j => section5Mass s r m (k + 2 - j))
              (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w)
              (k + 3 - r) l (k + 3 - (l + 1))
              (section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - l) w)
              (fun _ => h) (fun _ => h) ∂ℙ else 0))) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace hZ (fun z => Real.sqrt (z * t)) u
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega)) (k + 3 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => (hasDerivAt_section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w))
    (show ∀ᶠ z in 𝓝 w, ∀ j, 0 ≤ section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5InterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hv) ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w ∨
      (section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5InterpolationVariance_pos_or_eq_zero (mixedClockScheme ξ s) (mixedBeta ξ) (p := k + 2 - j)
        hr (by omega) ht (clock_mem_left_interval ξ s hr hv) hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz))
    (fun _ => h) (fun _ => h)
  simpa only [mixedLeftInterpolationOffDiagonal, offdiag_sqrt_time_derivative_mul ht.1 hw.1] using!
    H.const_mul (1 / (n : ℝ))

/-- Explicit trace-plus-heat formula for the actual right pressure.
The disorder coefficient is t/2 before site normalization. -/
theorem hasDerivAt_mixedRightInterpolationOffDiagonal_trace
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u v w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (mixedRightInterpolationOffDiagonal ξ s h Z r m t u v)
      ((1 / (n : ℝ)) * (t / 2 * (∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond
          (fun j => section5RightMass s r m (k + 2 - j))
          (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w)
          (k + 2 - r) (k + 3) (Real.sqrt (w * t) • Z ω)
          (hZ.w i) (hZ.w i) u (fun _ => h) (fun _ => h) ∂ℙ) +
        ∑ l : Fin (k + 3),
          (-(t * (mixedBeta ξ) ^ 2 * (section5RightRho (mixedClockScheme ξ s) r (ξ.clock v) (k + 2 - l + 1) -
            section5RightRho (mixedClockScheme ξ s) r (ξ.clock v) (k + 2 - l)))) *
          (if 0 < section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - l) w then
            ∫ ω, constrainedLevelVarianceD (Real.sqrt (w * t) • Z ω) u
              (fun j => section5RightMass s r m (k + 2 - j))
              (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w)
              (k + 2 - r) l (k + 3 - (l + 1))
              (section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - l) w)
              (fun _ => h) (fun _ => h) ∂ℙ else 0))) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace hZ (fun z => Real.sqrt (z * t)) u
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega)) (k + 2 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => (hasDerivAt_section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w))
    (show ∀ᶠ z in 𝓝 w, ∀ j, 0 ≤ section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5RightInterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hv) ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w ∨
      (section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5RightInterpolationVariance_pos_or_eq_zero (mixedClockScheme ξ s) (mixedBeta ξ) (p := k + 2 - j)
        hr (by omega) ht (clock_mem_right_interval ξ s hr hv) hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz))
    (fun _ => h) (fun _ => h)
  simpa only [mixedRightInterpolationOffDiagonal, offdiag_sqrt_time_derivative_mul ht.1 hw.1] using!
    H.const_mul (1 / (n : ℝ))

set_option maxHeartbeats 800000 in
/-- Actual Gaussian-averaged left pressure derivative, with all heat and
disorder terms under the same normalized split-replica weights. -/
theorem hasDerivAt_mixedLeftInterpolationOffDiagonal_replica
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr : r ≤ k + 1) {m t u v w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (mixedLeftInterpolationOffDiagonal ξ s h sk.U r m t u v)
      (mixedAveragedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) ξ u t
        (fun j => section5Mass s r m (k + 2 - j))
        (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w)
        (fun j => -(t * (ξ.first (section5Rho s r v (k + 2 - j + 1)) -
          ξ.first (section5Rho s r v (k + 2 - j)))))
        (k + 3 - r) (k + 3) (fun _ => h) (fun _ => h)) w := by
  apply (hasDerivAt_mixedLeftInterpolationOffDiagonal_trace ξ s h sk.hU hr hm ht hv hw).congr_deriv
  simpa only [section5Rho_clock, section5RightRho_clock, mul_assoc, mixed_first_increment] using!
    normalized_mixed_trace_heat_eq_replica hn ξ t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w)
    (fun j => -(t * (mixedBeta ξ)^2 * (section5Rho (mixedClockScheme ξ s) r (ξ.clock v) (k + 2 - j + 1) -
      section5Rho (mixedClockScheme ξ s) r (ξ.clock v) (k + 2 - j))))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => section5InterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hv) ⟨hw.1.le, hw.2.le⟩)
    (k + 3 - r) (k + 3)
    (fun l _ hz => section5InterpolationVelocity_zero_of_not_pos (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hv) hw.2 hz)
    (fun _ => h) (fun _ => h)

set_option maxHeartbeats 800000 in
/-- Actual Gaussian-averaged right pressure derivative with the dual cutoff.
Zero-mass and coincident-overlap cases are retained. -/
theorem hasDerivAt_mixedRightInterpolationOffDiagonal_replica
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {r : ℕ} (hr : r ≤ k + 1) {m t u v w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (mixedRightInterpolationOffDiagonal ξ s h sk.U r m t u v)
      (mixedAveragedReplicaPressureDerivative (fun ω => Real.sqrt (w * t) • sk.U ω) ξ u t
        (fun j => section5RightMass s r m (k + 2 - j))
        (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w)
        (fun j => -(t * (ξ.first (section5RightRho s r v (k + 2 - j + 1)) -
          ξ.first (section5RightRho s r v (k + 2 - j)))))
        (k + 2 - r) (k + 3) (fun _ => h) (fun _ => h)) w := by
  apply (hasDerivAt_mixedRightInterpolationOffDiagonal_trace ξ s h sk.hU hr hm ht hv hw).congr_deriv
  simpa only [section5Rho_clock, section5RightRho_clock, mul_assoc, mixed_first_increment] using!
    normalized_mixed_trace_heat_eq_replica hn ξ t sk
    (sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))) u
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j) w)
    (fun j => -(t * (mixedBeta ξ)^2 * (section5RightRho (mixedClockScheme ξ s) r (ξ.clock v) (k + 2 - j + 1) -
      section5RightRho (mixedClockScheme ξ s) r (ξ.clock v) (k + 2 - j))))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => section5RightInterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hv) ⟨hw.1.le, hw.2.le⟩)
    (k + 2 - r) (k + 3)
    (fun l _ hz => section5RightInterpolationVelocity_zero_of_not_pos (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hv) hw.2 hz)
    (fun _ => h) (fun _ => h)
/-- Closed-interval continuity of Talagrand's actual left second interpolation. -/
theorem continuousOn_mixedLeftInterpolationOffDiagonal {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) {r : ℕ} (hr : r ≤ k + 1)
    {m t u v : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q (r - 1)) (s.q r)) [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn (mixedLeftInterpolationOffDiagonal ξ s h Z r m t u v) (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => by unfold section5InterpolationVariance; fun_prop)
    (fun j w hw => section5InterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hv) hw)
    (k + 3 - r) (k + 3) (fun _ _ => h) (fun _ _ => h) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

/-- The actual dual right interpolation is continuous at both endpoints too. -/
theorem continuousOn_mixedRightInterpolationOffDiagonal {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) {r : ℕ} (hr : r ≤ k + 1)
    {m t u v : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc (s.q r) (s.q (r + 1))) [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn (mixedRightInterpolationOffDiagonal ξ s h Z r m t u v) (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock v) r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => by unfold section5RightInterpolationVariance; fun_prop)
    (fun j w hw => section5RightInterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hv) hw)
    (k + 2 - r) (k + 3) (fun _ _ => h) (fun _ _ => h) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

end FourPapersCommon
