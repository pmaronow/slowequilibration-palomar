module
public import FourPapersCommon.MixedLeftEndpoint
public import FourPapersCommon.MixedSecondInterpolationTrace

@[expose] public section

/-! Genuine Gaussian differentiation of the actual mixed left/right second
interpolation paths. Physical constraints are not replaced by clock variables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n k : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

private theorem sqrt_time_derivative_mul {t w : ℝ} (ht : 0 ≤ t) (hw : 0 < w) :
    t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
  by_cases hz : t = 0
  · simp [hz]
  · have hs : Real.sqrt (w * t) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos hw (lt_of_le_of_ne ht (Ne.symm hz)))).ne'
    field_simp

/-- Explicit trace-plus-heat formula for the actual left pressure.
The disorder coefficient is t/2 before site normalization. -/
theorem hasDerivAt_mixedLeftInterpolation_trace
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (mixedLeftInterpolation ξ s h Z r m t u)
      ((1 / (n : ℝ)) * (t / 2 * (∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond
          (fun j => section5Mass s r m (k + 2 - j))
          (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w)
          (k + 3 - r) (k + 3) (Real.sqrt (w * t) • Z ω)
          (hZ.w i) (hZ.w i) u (fun _ => h) (fun _ => h) ∂ℙ) +
        ∑ l : Fin (k + 3),
          (-(t * (mixedBeta ξ) ^ 2 * (section5Rho (mixedClockScheme ξ s) r (ξ.clock u) (k + 2 - l + 1) -
            section5Rho (mixedClockScheme ξ s) r (ξ.clock u) (k + 2 - l)))) *
          (if 0 < section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - l) w then
            ∫ ω, constrainedLevelVarianceD (Real.sqrt (w * t) • Z ω) u
              (fun j => section5Mass s r m (k + 2 - j))
              (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w)
              (k + 3 - r) l (k + 3 - (l + 1))
              (section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - l) w)
              (fun _ => h) (fun _ => h) ∂ℙ else 0))) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace hZ (fun z => Real.sqrt (z * t)) u
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega)) (k + 3 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => (hasDerivAt_section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w))
    (show ∀ᶠ z in 𝓝 w, ∀ j, 0 ≤ section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5InterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hu) ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w ∨
      (section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5InterpolationVariance_pos_or_eq_zero (mixedClockScheme ξ s) (mixedBeta ξ) (p := k + 2 - j)
        hr (by omega) ht (clock_mem_left_interval ξ s hr hu) hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz))
    (fun _ => h) (fun _ => h)
  simpa only [mixedLeftInterpolation, sqrt_time_derivative_mul ht.1 hw.1] using!
    H.const_mul (1 / (n : ℝ))

/-- Explicit trace-plus-heat formula for the actual right pressure.
The disorder coefficient is t/2 before site normalization. -/
theorem hasDerivAt_mixedRightInterpolation_trace
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z)
    {r : ℕ} (hr : r ≤ k + 1) {m t u w : ℝ} (hm : 0 ≤ m)
    (ht : t ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1)))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt (mixedRightInterpolation ξ s h Z r m t u)
      ((1 / (n : ℝ)) * (t / 2 * (∫ ω, ∑ i : hZ.ι, (hZ.τ i : ℝ) *
        constrainedPairFieldCascadeSecond
          (fun j => section5RightMass s r m (k + 2 - j))
          (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w)
          (k + 2 - r) (k + 3) (Real.sqrt (w * t) • Z ω)
          (hZ.w i) (hZ.w i) u (fun _ => h) (fun _ => h) ∂ℙ) +
        ∑ l : Fin (k + 3),
          (-(t * (mixedBeta ξ) ^ 2 * (section5RightRho (mixedClockScheme ξ s) r (ξ.clock u) (k + 2 - l + 1) -
            section5RightRho (mixedClockScheme ξ s) r (ξ.clock u) (k + 2 - l)))) *
          (if 0 < section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - l) w then
            ∫ ω, constrainedLevelVarianceD (Real.sqrt (w * t) • Z ω) u
              (fun j => section5RightMass s r m (k + 2 - j))
              (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w)
              (k + 2 - r) l (k + 3 - (l + 1))
              (section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - l) w)
              (fun _ => h) (fun _ => h) ∂ℙ else 0))) w := by
  have H := hasDerivAt_constrainedPairGaussian_path_trace hZ (fun z => Real.sqrt (z * t)) u
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega)) (k + 2 - r) (k + 3)
    (hasDerivAt_sqrt_mul_time ht.1 hw.1)
    (fun j _ => (hasDerivAt_section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w))
    (show ∀ᶠ z in 𝓝 w, ∀ j, 0 ≤ section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) z from by
      filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
      intro j
      exact section5RightInterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hu) ⟨hz.1.le, hz.2.le⟩)
    (show ∀ j < k + 3,
      0 < section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) w ∨
      (section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j) =ᶠ[𝓝 w] fun _ => 0) from by
      intro j hj
      rcases section5RightInterpolationVariance_pos_or_eq_zero (mixedClockScheme ξ s) (mixedBeta ξ) (p := k + 2 - j)
        hr (by omega) ht (clock_mem_right_interval ξ s hr hu) hw.2 with hp | hz
      · exact Or.inl hp
      · exact Or.inr (Eventually.of_forall hz))
    (fun _ => h) (fun _ => h)
  simpa only [mixedRightInterpolation, sqrt_time_derivative_mul ht.1 hw.1] using!
    H.const_mul (1 / (n : ℝ))


end FourPapersCommon
