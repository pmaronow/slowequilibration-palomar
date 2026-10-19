-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureOriginalConditionalPointMean
public import SlowEquilibration.SphericalTAPLatitudeLIntegralChange

@[expose] public section

/-! Conditional Fubini for the original pure Hamiltonian, retaining the
actual restricted spherical partition and the actual value-gradient posterior. -/

namespace SlowEquilibration.SphericalPureOriginalConditionalBandFubini
noncomputable section
open MeasureTheory Set SphericalModel SphericalMarkedWindows
open SphericalGaussianJet
open SphericalPureOriginalConditionalPointMean
open SphericalTAPCriticalPureLatitudeVariance
set_option autoImplicit false

def originalPureMeanProfile (n p : ℕ) (alpha β H : ℝ) (u w : Vector (n+1)) : ℝ :=
  Real.exp (β*H*(overlap u w)^p+
    (n+1 : ℕ)*β^2*sourcePureLatitudeVariance p alpha (overlap u w)/2)

theorem originalPureMeanProfile_continuous (n p : ℕ) (alpha β H : ℝ)
    (u : Vector (n+1)) : Continuous (originalPureMeanProfile n p alpha β H u) := by
  unfold originalPureMeanProfile overlap sourcePureLatitudeVariance
  fun_prop

theorem pure_original_conditioned_point_exp_integrable
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (u w : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (hw : ‖w‖^2=(n+1 : ℕ)) (β H : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    Integrable (fun J : Disorder (n+1) μ.maxDegree =>
      Real.exp (β*field (mixtureCoefficients μ) J w))
      (valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) := by
  dsimp only
  have hm := pure_original_conditioned_point_exp_mean n p hp alpha halpha
    hQ u w hu hw rfl β H
  dsimp only at hm
  by_contra hnot
  rw [integral_undef hnot] at hm
  exact (Real.exp_pos _).ne' hm.symm

/-- The original-field exponential is jointly integrable under the true
pure critical-point posterior and the uniform spherical law. -/
theorem pure_original_conditioned_exp_prod_integrable
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) (β H : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    Integrable (fun z : Disorder (n+1) μ.maxDegree × Vector (n+1) =>
      Real.exp (β*field (mixtureCoefficients μ) z.1 z.2))
      ((valueConditionedLaw c u hu (s*H/(n+1 : ℕ))).prod (sphereLaw (n+1))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  let P := valueConditionedLaw c u hu (s*H/(n+1 : ℕ))
  let : IsProbabilityMeasure P := by
    unfold P valueConditionedLaw
    infer_instance
  let f := fun z : Disorder (n+1) μ.maxDegree × Vector (n+1) =>
    Real.exp (β*field (mixtureCoefficients μ) z.1 z.2)
  have hc : Continuous f := by
    dsimp [f]
    exact Real.continuous_exp.comp
      (continuous_const.mul (field_jointContinuous (mixtureCoefficients μ)))
  apply (integrable_prod_iff' hc.measurable.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [sphereLaw_support (show 1 ≤ n+1 by omega)] with w hw
    exact pure_original_conditioned_point_exp_integrable n p hp alpha halpha
      hQ u w hu hw β H
  · have hprof : Integrable (originalPureMeanProfile n p alpha β H u)
        (sphereLaw (n+1)) :=
      integrable_sphere_of_continuous (by omega)
        (originalPureMeanProfile_continuous n p alpha β H u)
    apply hprof.congr
    filter_upwards [sphereLaw_support (show 1 ≤ n+1 by omega)] with w hw
    change originalPureMeanProfile n p alpha β H u w =
      ∫ J, ‖Real.exp (β*field (mixtureCoefficients μ) J w)‖ ∂P
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [originalPureMeanProfile, P, c, s, μ] using
      (pure_original_conditioned_point_exp_mean n p hp alpha halpha
        hQ u w hu hw rfl β H).symm

/-- Fubini for any Borel overlap set: the conditioned band partition mean
is exactly an ordinary spherical integral of the explicit pointwise mean. -/
theorem pure_original_conditioned_band_mean_sphere
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (β H : ℝ) (I : Set ℝ) (hI : MeasurableSet I) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u I) ∂valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) =
      ∫ w in overlapRegion u I,
        originalPureMeanProfile n p alpha β H u w ∂sphereLaw (n+1) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  let P := valueConditionedLaw c u hu (s*H/(n+1 : ℕ))
  let : IsProbabilityMeasure P := by
    unfold P valueConditionedLaw
    infer_instance
  let B := overlapRegion u I
  have hB : MeasurableSet B := overlapRegion_measurable u hI
  let f := fun z : Disorder (n+1) μ.maxDegree × Vector (n+1) =>
    Real.exp (β*field (mixtureCoefficients μ) z.1 z.2)
  have hjoint : Integrable (fun z => B.indicator (fun w => f (z.1,w)) z.2)
      (P.prod (sphereLaw (n+1))) :=
    (pure_original_conditioned_exp_prod_integrable n p hp alpha halpha
      hQ u hu β H).indicator (hB.preimage measurable_snd)
  change Integrable (Function.uncurry (fun J w => B.indicator
    (fun w => f (J,w)) w)) (P.prod (sphereLaw (n+1))) at hjoint
  have hswap := integral_integral_swap hjoint
  calc
    _ = ∫ J, (∫ w, B.indicator (fun w => f (J,w)) w
        ∂sphereLaw (n+1)) ∂P := by
      apply integral_congr_ae
      exact .of_forall fun J => by
        change partitionOn β (field (mixtureCoefficients μ) J) B =
          ∫ w, B.indicator (fun w => f (J,w)) w ∂sphereLaw (n+1)
        unfold partitionOn
        rw [integral_indicator hB]
    _ = ∫ w, (∫ J, B.indicator (fun w => f (J,w)) w ∂P)
        ∂sphereLaw (n+1) := hswap
    _ = ∫ w, B.indicator (originalPureMeanProfile n p alpha β H u) w
        ∂sphereLaw (n+1) := by
      apply integral_congr_ae
      filter_upwards [sphereLaw_support (show 1 ≤ n+1 by omega)] with w hw
      by_cases hwB : w ∈ B
      · have hfun : (fun J => B.indicator (fun w => f (J,w)) w) =
            (fun J => f (J,w)) := by
          funext J
          exact Set.indicator_of_mem hwB (fun w => f (J,w))
        rw [hfun, Set.indicator_of_mem hwB]
        simpa only [originalPureMeanProfile, f, P, c, s, μ] using
          pure_original_conditioned_point_exp_mean n p hp alpha halpha
            hQ u w hu hw rfl β H
      · have hfun : (fun J => B.indicator (fun w => f (J,w)) w) =
            (fun _ => (0:ℝ)) := by
          funext J
          exact Set.indicator_of_notMem hwB (fun w => f (J,w))
        rw [hfun, Set.indicator_of_notMem hwB]
        simp
    _ = _ := integral_indicator hB

end
end SlowEquilibration.SphericalPureOriginalConditionalBandFubini
