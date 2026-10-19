module
public import FourPapersCommon.MixedSecondInterpolationDerivative

@[expose] public section

/-! Endpoint continuity of the actual mixed second interpolation, including
zero field variances and zero cascade masses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology Set SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
namespace FourPapersCommon
universe u
variable {n : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

/-- Closed-interval continuity of Talagrand's actual left second interpolation. -/
theorem continuousOn_mixedLeftInterpolation {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) {r : ℕ} (hr : r ≤ k + 1)
    {m t u : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q (r - 1)) (s.q r)) [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn (mixedLeftInterpolation ξ s h Z r m t u) (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5Mass s r m (k + 2 - j))
    (fun j => section5InterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j))
    (fun j => section5Mass_nonneg s hr hm (by omega))
    (fun j => by unfold section5InterpolationVariance; fun_prop)
    (fun j w hw => section5InterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_left_interval ξ s hr hu) hw)
    (k + 3 - r) (k + 3) (fun _ _ => h) (fun _ _ => h) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

/-- The actual dual right interpolation is continuous at both endpoints too. -/
theorem continuousOn_mixedRightInterpolation {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {Z : Ω → EnergySpace n} (hZ : IsGaussianHilbert Z) {r : ℕ} (hr : r ≤ k + 1)
    {m t u : ℝ} (hm : 0 ≤ m) (ht : t ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc (s.q r) (s.q (r + 1))) [Nonempty (AT.ConstrainedPair n u)] :
    ContinuousOn (mixedRightInterpolation ξ s h Z r m t u) (Set.Icc (0 : ℝ) 1) := by
  have H := continuousOn_constrainedPairGaussian_path hZ u isCompact_Icc
    (fun w => Real.sqrt (w * t)) (by fun_prop)
    (fun j => section5RightMass s r m (k + 2 - j))
    (fun j => section5RightInterpolationVariance (mixedClockScheme ξ s) (mixedBeta ξ) t (ξ.clock u) r (k + 2 - j))
    (fun j => section5RightMass_nonneg s hr hm (by omega))
    (fun j => by unfold section5RightInterpolationVariance; fun_prop)
    (fun j w hw => section5RightInterpolationVariance_nonneg (mixedClockScheme ξ s) (mixedBeta ξ) hr (by omega) ht (clock_mem_right_interval ξ s hr hu) hw)
    (k + 2 - r) (k + 3) (fun _ _ => h) (fun _ _ => h) continuousOn_const continuousOn_const
  exact H.const_mul (1 / (n : ℝ))

end FourPapersCommon
