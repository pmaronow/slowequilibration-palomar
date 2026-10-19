-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorPairIntegrable
public import SlowEquilibration.SourcePureCapPosteriorBandSecondFubini

/-! Genuine second-moment integrability of an arbitrary Borel-band
partition under the original pure critical-point posterior. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelBandSquareIntegrable
noncomputable section
open Set MeasureTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet
open SourcePureCapPosteriorPairIntegrable
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_conditioned_borel_band_square_integrable
    (n p : ℕ) (hp : 2 ≤ p)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (β H : ℝ) {I : Set ℝ} (hI : MeasurableSet I) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) 1
    let B := overlapRegion u I
    Integrable (fun J =>
      (partitionOn β (field (mixtureCoefficients μ) J) B)^2)
      (valueConditionedLaw c u hu (H/(n+1 : ℕ))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let P := valueConditionedLaw c u hu (H/(n+1 : ℕ))
  let ν := (sphereLaw (n+1)).prod (sphereLaw (n+1))
  let B := overlapRegion u I
  have hB : MeasurableSet B := overlapRegion_measurable u hI
  have hBB : MeasurableSet (B ×ˢ B) := hB.prod hB
  let f := fun z : Disorder (n+1) μ.maxDegree ×
      (Vector (n+1) × Vector (n+1)) =>
    Real.exp (β*field (mixtureCoefficients μ) z.1 z.2.1)*
      Real.exp (β*field (mixtureCoefficients μ) z.1 z.2.2)
  have hJoint : Integrable (fun z =>
      (B ×ˢ B).indicator (fun yz => f (z.1,yz)) z.2) (P.prod ν) :=
    (pure_original_conditioned_exp_pair_prod_integrable n p hp 1
      (by positivity) u hu β H).indicator (hBB.preimage measurable_snd)
  have hOuter : Integrable (fun J =>
      ∫ z : Vector (n+1) × Vector (n+1),
        (B ×ˢ B).indicator (fun yz => f (J,yz)) z ∂ν) P :=
    hJoint.integral_prod_left
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
  apply hOuter.congr
  exact .of_forall fun J => (hpart J).symm

end
end SlowEquilibration.SourcePureCapBorelBandSquareIntegrable
