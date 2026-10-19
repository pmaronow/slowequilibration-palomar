-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedLowSumIntegral

@[expose] public section

/-! The deterministic below-window exponential integral in the nonnegative
extended-real form produced by actual marked Kac--Rice. -/

namespace SlowEquilibration.SourceMixedLowSumENNIntegral
noncomputable section
open MeasureTheory Set
open SourceMixedLowSumIntegral
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem intensity_palm_below_window_lintegral
    (dens palm : ℝ → ℝ) {N m E₀ τ M β cPlus C₂ Cdens C₁ D : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hC₂ : 0 < C₂)
    (hCdens : 0 ≤ Cdens) (hC₁ : 0 ≤ C₁) (hD : 0 ≤ D)
    (hgap : 0 < β-cPlus)
    (hcenter : 3*|m-N*E₀| ≤ τ*N)
    (hτ : τ ≤ (β-cPlus)/(4*C₂))
    (hP0 : ∀ H ∈ Icc (N*(E₀-τ)) (m-M), 0 ≤ palm H)
    (hDens : ∀ H ∈ Icc (N*(E₀-τ)) (m-M),
      dens H ≤ Cdens*Real.exp (cPlus*(m-H)))
    (hPalm : ∀ H ∈ Icc (N*(E₀-τ)) (m-M),
      palm H ≤ C₁*D*Real.exp
        (β*(H-m)+C₂*(H-N*E₀)^2/N)) :
    (∫⁻ H in Icc (N*(E₀-τ)) (m-M),
      ENNReal.ofReal (dens H*palm H)) ≤
      ENNReal.ofReal
        ((Cdens*C₁*D*Real.exp (C₂*(m-N*E₀)^2/N)) /
          ((β-cPlus)/2)*Real.exp (-((β-cPlus)/2)*M)) := by
  let a : ℝ := (β-cPlus)/2
  let A : ℝ := Cdens*C₁*D*Real.exp (C₂*(m-N*E₀)^2/N)
  have ha : 0 < a := by dsimp [a]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmajorInt : IntegrableOn (fun H : ℝ => A*Real.exp (a*(H-m)))
      (Icc (N*(E₀-τ)) (m-M)) := by
    have hcont : Continuous (fun H : ℝ => A*Real.exp (a*(H-m))) := by
      fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hmajorNN : ∀ H, 0 ≤ A*Real.exp (a*(H-m)) := by
    intro H
    positivity
  have hlin :
      (∫⁻ H in Icc (N*(E₀-τ)) (m-M),
        ENNReal.ofReal (dens H*palm H)) ≤
      ∫⁻ H in Icc (N*(E₀-τ)) (m-M),
        ENNReal.ofReal (A*Real.exp (a*(H-m))) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with H hH
    exact ENNReal.ofReal_le_ofReal
      (intensity_palm_product_below_window dens palm hN hC₂
        hCdens hC₁ hD (by linarith [hH.2,hM]) hH.1
        hcenter hτ (hP0 H hH) (hDens H hH) (hPalm H hH))
  have hmajorEq :
      (∫⁻ H in Icc (N*(E₀-τ)) (m-M),
        ENNReal.ofReal (A*Real.exp (a*(H-m)))) =
      ENNReal.ofReal
        (∫ H in Icc (N*(E₀-τ)) (m-M),
          A*Real.exp (a*(H-m)) ∂volume) := by
    exact (ofReal_integral_eq_lintegral_ofReal hmajorInt
      (.of_forall hmajorNN)).symm
  rw [hmajorEq] at hlin
  exact hlin.trans (ENNReal.ofReal_le_ofReal
    (integral_below_window_exp_bound
      (fun H => A*Real.exp (a*(H-m))) (N*(E₀-τ)) m M a A
      ha hA hmajorInt (by intro H hH; exact le_refl _)))

end
end SlowEquilibration.SourceMixedLowSumENNIntegral
