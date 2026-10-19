-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorPairIntegrable

/-! The original pure critical-point posterior band second moment is an
exact two-spin spherical integral, with no assumed moment comparison. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorBandSecondFubini
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalPureOriginalConditionalBandFubini
open SourcePureCapPosteriorPairIntegrable
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_conditioned_band_sq_sphere
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (β H : ℝ) (I : Set ℝ) (hI : MeasurableSet I) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) 1
    let B := overlapRegion u I
    (∫ J, (partitionOn β (field (mixtureCoefficients μ) J) B)^2
      ∂valueConditionedLaw c u hu (H/(n+1 : ℕ))) =
      ∫ z : Vector (n+1) × Vector (n+1),
        (B ×ˢ B).indicator (originalPurePairMeanProfile n p alpha β H u) z
        ∂(sphereLaw (n+1)).prod (sphereLaw (n+1)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let P := valueConditionedLaw c u hu (H/(n+1 : ℕ))
  let : IsProbabilityMeasure P := by
    unfold P valueConditionedLaw
    infer_instance
  let ν := (sphereLaw (n+1)).prod (sphereLaw (n+1))
  let B := overlapRegion u I
  have hB : MeasurableSet B := overlapRegion_measurable u hI
  have hBB : MeasurableSet (B ×ˢ B) := hB.prod hB
  let f := fun z : Disorder (n+1) μ.maxDegree ×
      (Vector (n+1) × Vector (n+1)) =>
    Real.exp (β*field (mixtureCoefficients μ) z.1 z.2.1)*
      Real.exp (β*field (mixtureCoefficients μ) z.1 z.2.2)
  have hjoint : Integrable (fun z => (B ×ˢ B).indicator (fun yz => f (z.1,yz)) z.2)
      (P.prod ν) :=
    (pure_original_conditioned_exp_pair_prod_integrable n p hp alpha halpha
      u hu β H).indicator (hBB.preimage measurable_snd)
  change Integrable (Function.uncurry (fun J z =>
    (B ×ˢ B).indicator (fun yz => f (J,yz)) z)) (P.prod ν) at hjoint
  have hswap := integral_integral_swap hjoint
  have hpart (J : Disorder (n+1) μ.maxDegree) :
      (partitionOn β (field (mixtureCoefficients μ) J) B)^2 =
      ∫ z : Vector (n+1) × Vector (n+1),
        (B ×ˢ B).indicator (fun yz => f (J,yz)) z ∂ν := by
    have heq : (fun z : Vector (n+1) × Vector (n+1) =>
        (B ×ˢ B).indicator (fun yz => f (J,yz)) z) =
        (fun z => B.indicator
          (fun w => Real.exp (β*field (mixtureCoefficients μ) J w)) z.1*
          B.indicator
          (fun w => Real.exp (β*field (mixtureCoefficients μ) J w)) z.2) := by
      funext z
      by_cases hz₁ : z.1 ∈ B <;> by_cases hz₂ : z.2 ∈ B <;>
        simp [f,hz₁,hz₂]
    rw [heq]
    unfold partitionOn
    rw [← integral_indicator hB]
    simpa only [pow_two,ν] using
      (integral_prod_mul (μ := sphereLaw (n+1)) (ν := sphereLaw (n+1))
        (B.indicator fun w => Real.exp (β*field (mixtureCoefficients μ) J w))
        (B.indicator fun w => Real.exp (β*field (mixtureCoefficients μ) J w))).symm
  calc
    _ = ∫ J, (∫ z : Vector (n+1) × Vector (n+1),
        (B ×ˢ B).indicator (fun yz => f (J,yz)) z ∂ν) ∂P := by
      apply integral_congr_ae
      exact .of_forall hpart
    _ = ∫ z, (∫ J, (B ×ˢ B).indicator (fun yz => f (J,yz)) z ∂P) ∂ν := hswap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [sphereLaw_pair_support (by omega : 1 ≤ n+1)] with z hz
      by_cases hzBB : z ∈ B ×ˢ B
      · have heq : (fun J : Disorder (n+1) μ.maxDegree =>
            (B ×ˢ B).indicator (fun yz => f (J,yz)) z) =
            (fun J => f (J,z)) := by
          funext J
          exact Set.indicator_of_mem hzBB (fun yz => f (J,yz))
        rw [heq,Set.indicator_of_mem hzBB]
        exact pure_original_conditioned_pair_exp_eq_profile n p hp alpha halpha
          u z.1 z.2 hu hz.1 hz.2 β H
      · have heq : (fun J : Disorder (n+1) μ.maxDegree =>
            (B ×ˢ B).indicator (fun yz => f (J,yz)) z) =
            (fun _ => (0:ℝ)) := by
          funext J
          exact Set.indicator_of_notMem hzBB (fun yz => f (J,yz))
        rw [heq,Set.indicator_of_notMem hzBB]
        simp

end
end SlowEquilibration.SourcePureCapPosteriorBandSecondFubini
