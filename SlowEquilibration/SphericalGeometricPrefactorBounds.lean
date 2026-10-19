-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GammaHalfStirling
public import SlowEquilibration.SphericalGeometricPrefactorRates

/-! Bounded multiplicative normalization of the genuine round-sphere
Kac--Rice prefactor, with no dimension-dependent loss. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory Set
open SphericalModel SphericalGaussianJet WholeFieldRegression
open SphereChartVolume SphereAreaAsymptotics
open scoped ENNReal
noncomputable section

theorem manuscriptRoundVolume_log_error_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      |Real.log (manuscriptRoundVolume (n+1) univ).toReal -
        (n+2 : ℕ) * ((1 + Real.log (2 * Real.pi))/2)| ≤ B := by
  obtain ⟨B,hB,hΓ⟩ := gamma_half_integer_log_remainder_bound
  refine ⟨|Real.log 2|/2+B, by positivity, ?_⟩
  intro n
  have h := hΓ (n+2) (by omega)
  rw [manuscriptRoundVolume_log_mass n,
    Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero]
  have hN : (0 : ℝ) < n+2 := by positivity
  rw [Real.log_div (by positivity : ((n+2:ℕ):ℝ)≠0) (by norm_num : (2:ℝ)≠0)] at h
  push_cast at h ⊢
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [le_abs_self (Real.log 2), neg_le_abs (Real.log 2)]

/-- The true geometric prefactor differs from its exact leading exponential
by constants independent of the ambient dimension. -/
theorem sphereKRPrefactor_log_error_bound (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      |Real.log (sphereKRPrefactor (n+1) μ Q).toReal -
        (n+2 : ℕ) * ((1 - Real.log (Q * μ.xi1 Q))/2)| ≤ B := by
  obtain ⟨B,hB,harea⟩ := manuscriptRoundVolume_log_error_bound
  refine ⟨B + |Real.log (2 * Real.pi * (Q * μ.xi1 Q))|/2, by positivity, ?_⟩
  intro n
  have h := harea n
  have ha := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hlog : Real.log (2 * Real.pi * (Q * μ.xi1 Q)) =
      Real.log (2 * Real.pi) + Real.log (Q * μ.xi1 Q) :=
    Real.log_mul (mul_pos (by norm_num) Real.pi_pos).ne' ha.ne'
  rw [sphereKRPrefactor_log n μ hQ]
  rw [abs_le] at h ⊢
  push_cast at h ⊢
  constructor <;> nlinarith [le_abs_self (Real.log (2 * Real.pi * (Q * μ.xi1 Q))),
    neg_le_abs (Real.log (2 * Real.pi * (Q * μ.xi1 Q)))]

end
end SlowEquilibration.SphericalMarkedWindows
