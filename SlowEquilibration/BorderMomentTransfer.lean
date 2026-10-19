-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.OneBorderDeterminant
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Genuine determinant-border moment transfer

Cauchy--Schwarz applies on the actual common probability space, without any
independence of the bulk matrix and its border. Integrability and ordinary
expectations are explicit, including arbitrary nonnegative real moment powers.
-/

@[expose] public section

namespace SlowEquilibration.BorderMomentTransfer

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- True product domination transfers second moments to an ordinary real
moment, with the required integrability proved rather than silently defaulted. -/
theorem moment_of_exponential_domination (D Y B : Ω → ℝ)
    (hD : Measurable D) (hY : Measurable Y) (hB : Measurable B)
    (hDnonneg : ∀ x, 0 ≤ D x) (hBnonneg : ∀ x, 0 ≤ B x)
    (hdom : ∀ x, D x ≤ Real.exp (Y x) * B x)
    {r : ℝ} (hr : 0 ≤ r)
    (hYmoment : Integrable (fun x => Real.exp (2 * r * Y x)) μ)
    (hBmoment : Integrable (fun x => B x ^ (2 * r)) μ) :
    Integrable (fun x => D x ^ r) μ ∧
      (∫ x, D x ^ r ∂μ) ≤
        Real.sqrt (∫ x, Real.exp (2 * r * Y x) ∂μ) * Real.sqrt (∫ x, B x ^ (2 * r) ∂μ) := by
  have hf : MemLp (fun x => Real.exp (r * Y x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq ((measurable_const.mul hY).exp.aestronglyMeasurable)).mpr
    convert hYmoment using 1
    funext x
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [Pi.mul_apply]
    ring
  have heB (x : Ω) : (B x ^ r) ^ (2 : ℕ) = B x ^ (2 * r) := by
    simpa only [Real.rpow_two, mul_comm] using (Real.rpow_mul (hBnonneg x) r 2).symm
  have hg : MemLp (fun x => B x ^ r) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hB.pow_const r).aestronglyMeasurable).mpr
    simpa only [heB] using hBmoment
  have hprod : Integrable (fun x => Real.exp (r * Y x) * B x ^ r) μ :=
    (memLp_one_iff_integrable).mp (hf.mul hg)
  have hpoint (x : Ω) : D x ^ r ≤ Real.exp (r * Y x) * B x ^ r := by
    have h := Real.rpow_le_rpow (hDnonneg x) (hdom x) hr
    rw [Real.mul_rpow (Real.exp_pos _).le (hBnonneg x), ← Real.exp_mul] at h
    simpa only [mul_comm (Y x) r] using h
  have hIntD : Integrable (fun x => D x ^ r) μ := by
    apply hprod.mono' (hD.pow_const r).aestronglyMeasurable
    exact ae_of_all μ (fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hDnonneg x) r)]
      exact hpoint x)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    (ae_of_all μ (fun x => (Real.exp_pos (r * Y x)).le))
    (ae_of_all μ (fun x => Real.rpow_nonneg (hBnonneg x) r))
    (by simpa using hf) (by simpa using hg)
  have hExp (x : Ω) : Real.exp (r * Y x) ^ (2 : ℝ) = Real.exp (2 * r * Y x) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hpow (x : Ω) : (B x ^ r) ^ (2 : ℝ) = B x ^ (2 * r) := by
    rw [← Real.rpow_mul (hBnonneg x)]
    congr 1
    ring
  simp only [hExp, hpow, ← Real.sqrt_eq_rpow] at hCS
  exact ⟨hIntD, (integral_mono hIntD hprod hpoint).trans hCS⟩

/-- The source border factor can be compared with |a|+‖u‖² using only the
fixed clipping radius, for every actual border and every bulk dimension. -/
lemma border_factor_bound {ι : Type*} [Fintype ι] {rho : ℝ} (_hrho : 0 < rho)
    (a : ℝ) (u : ι → ℝ) :
    |a| + (∑ i, u i ^ 2) / rho ≤ max (1 : ℝ) (1 / rho) * (|a| + ∑ i, u i ^ 2) := by
  have hs : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have ha := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (1 / rho)) (abs_nonneg a)
  have hu := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (1 / rho)) hs
  calc
    _ = 1 * |a| + (1 / rho) * (∑ i, u i ^ 2) := by ring
    _ ≤ max (1 : ℝ) (1 / rho) * |a| + max (1 : ℝ) (1 / rho) * (∑ i, u i ^ 2) := add_le_add ha hu
    _ = _ := by ring

end
end SlowEquilibration.BorderMomentTransfer
