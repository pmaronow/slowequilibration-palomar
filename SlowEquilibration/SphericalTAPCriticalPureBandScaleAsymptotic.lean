-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureBandScaleIdentity
public import SlowEquilibration.SphericalLatitudeNormalizationAsymptotic

@[expose] public section

/-! The source proper-pure Palm scale has a sharp coarea prefactor. -/

namespace SlowEquilibration.SphericalTAPCriticalPureBandScaleAsymptotic
noncomputable section
open Filter SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalBandSectionBridge
open scoped Topology
set_option autoImplicit false

theorem sourcePure_bandScale_normalized_ratio
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    (n : ℕ) (hn : 2 ≤ n) (e mN : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    (sourceCriticalBandScale n μ h.overlap_range β mN *
        Real.exp (β*(((n+1:ℕ):ℝ)*e-mN))) /
      Real.exp (((n+1:ℕ):ℝ)*
        (CSParisiMeasure.variationalValue μ β+β*(e-E))) =
      (1-Q)^(-(3/2:ℝ)) *
        ((SphericalModel.latitudeNormalization n).toReal /
          Real.sqrt (((n+1:ℕ):ℝ))) := by
  dsimp only
  rw [SphericalTAPCriticalPureBandScaleIdentity.sourcePure_bandScale_exact_identity
    p hp alpha halpha h n hn e mN]
  field_simp

/-- The exact normalized latitude Palm scale converges to its genuine
Gaussian coarea constant, uniformly in the choices of energy and centering
because the ratio is independent of both at every finite dimension. -/
theorem sourcePure_bandScale_normalized_ratio_tendsto
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    (e mN : ℕ → ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    Filter.Tendsto (fun n : ℕ =>
      (sourceCriticalBandScale n μ h.overlap_range β (mN n) *
        Real.exp (β*(((n+1:ℕ):ℝ)*e n-mN n))) /
        Real.exp (((n+1:ℕ):ℝ)*
          (CSParisiMeasure.variationalValue μ β+β*(e n-E))))
      Filter.atTop
      (nhds ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi))) := by
  dsimp only
  have heq : (fun n : ℕ =>
      (sourceCriticalBandScale n (FiniteMixture.pure p hp alpha halpha)
          h.overlap_range β (mN n) *
        Real.exp (β*(((n+1:ℕ):ℝ)*e n-mN n))) /
        Real.exp (((n+1:ℕ):ℝ)*
          (CSParisiMeasure.variationalValue
            (FiniteMixture.pure p hp alpha halpha) β+
            β*(e n-markE (FiniteMixture.pure p hp alpha halpha) β x Q)))) =ᶠ[atTop]
      (fun n : ℕ => (1-Q)^(-(3/2:ℝ)) *
        ((SphericalModel.latitudeNormalization n).toReal /
          Real.sqrt (((n+1:ℕ):ℝ)))) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact sourcePure_bandScale_normalized_ratio
      p hp alpha halpha h n hn (e n) (mN n)
  have ht := SphericalModel.latitudeNormalization_toReal_div_sqrt_tendsto.const_mul
    ((1-Q)^(-(3/2:ℝ)))
  have ht' := ht.congr' heq.symm
  simpa only [mul_one_div] using ht'

end
end SlowEquilibration.SphericalTAPCriticalPureBandScaleAsymptotic
