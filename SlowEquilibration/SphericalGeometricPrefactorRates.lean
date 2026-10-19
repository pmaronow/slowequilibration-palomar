-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GammaLogAsymptotics
public import SlowEquilibration.RoundSphereArea
public import SlowEquilibration.SphericalScoreDensityRates

/-! The true sphere-area and Kac--Rice geometric prefactor rates. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function Filter
open SphericalModel SphericalGaussianJet SphericalSequentialRegression
open SphereChartVolume SphereAreaAsymptotics WholeFieldRegression
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma manuscriptRoundVolume_log_mass (n : ℕ) :
    Real.log (manuscriptRoundVolume (n+1) univ).toReal =
      ((n+2 : ℝ)+1)/2 * Real.log (n+2 : ℝ) +
      (n+2 : ℝ)/2 * Real.log Real.pi - Real.log (Real.Gamma ((n+2 : ℝ)/2+1)) := by
  rw [manuscriptRoundVolume_mass_gamma]
  have hN : (0 : ℝ) < n+2 := by positivity
  have hG : 0 < Real.Gamma ((n+2 : ℝ)/2+1) := Real.Gamma_pos_of_pos (by positivity)
  simp only [Nat.cast_add, Nat.cast_one, show (n:ℝ)+1+1=n+2 by ring]
  rw [ENNReal.toReal_ofReal (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hN.ne', Real.log_pow, Real.log_div (by positivity) hG.ne',
    Real.log_pow, Real.log_sqrt hN.le, Real.log_sqrt Real.pi_pos.le]
  push_cast
  ring

/-- The logarithmic rate is for the literal round measure already used in
the actual critical-count formula, at radius `sqrt N`. -/
theorem manuscriptRoundVolume_log_rate :
    Tendsto (fun n : ℕ => Real.log (manuscriptRoundVolume (n+1) univ).toReal / (n+2 : ℕ))
      atTop (𝓝 ((1 + Real.log (2 * Real.pi))/2)) := by
  have hN : Tendsto (fun n : ℕ => (n:ℝ)+2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2:ℝ)))
  have hG := gamma_log_rate.comp (hN.atTop_div_const (by norm_num : (0:ℝ)<2))
  have h := ((hG.neg.div_const 2).add (tendsto_const_nhds
    (x := (Real.log 2 + Real.log Real.pi)/2))).add (log_dimension_div_tendsto.div_const 2)
  convert h using 1
  · funext n
    rw [manuscriptRoundVolume_log_mass n]
    dsimp only [Function.comp_def]
    rw [Real.log_div (by positivity : (n:ℝ)+2 ≠ 0) (by norm_num : (2:ℝ)≠0)]
    push_cast
    field_simp
    ring
  · rw [Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero]
    congr 1
    ring

lemma sphereKRPrefactor_log (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    Real.log (sphereKRPrefactor (n+1) μ Q).toReal =
      Real.log (manuscriptRoundVolume (n+1) univ).toReal -
        (n+1 : ℝ)/2 * Real.log (2 * Real.pi * (Q * μ.xi1 Q)) := by
  have ha : 0 < 2 * Real.pi * (Q * μ.xi1 Q) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (mul_pos hQ (mixture_xi1_pos μ hQ))
  have hv := ENNReal.toReal_pos (manuscriptRoundVolume_mass_ne_zero (n+1))
    (manuscriptRoundVolume_mass_ne_top (n+1))
  rw [sphereKRPrefactor_physical (n+1) μ hQ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ha _).le,
    Real.log_mul hv.ne' (Real.rpow_pos_of_pos ha _).ne', Real.log_rpow ha]
  push_cast
  ring

/-- The actual geometric Kac--Rice prefactor contributes exactly
`(1-log a_Q)/2` per ambient dimension. -/
theorem sphereKRPrefactor_log_rate (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    Tendsto (fun n : ℕ => Real.log (sphereKRPrefactor (n+1) μ Q).toReal / (n+2 : ℕ))
      atTop (𝓝 ((1 - Real.log (Q * μ.xi1 Q))/2)) := by
  have ha := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hr := GOEPhysicalPotential.dimension_ratio_tendsto 1
  have h := manuscriptRoundVolume_log_rate.sub
    (hr.mul_const (Real.log (2 * Real.pi * (Q * μ.xi1 Q))/2))
  convert h using 1
  · funext n
    rw [sphereKRPrefactor_log n μ hQ]
    push_cast
    ring
  · rw [Real.log_mul (mul_pos (by norm_num) Real.pi_pos).ne' ha.ne']
    congr 1
    ring

end
end SlowEquilibration.SphericalMarkedWindows
