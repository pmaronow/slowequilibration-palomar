-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLogPolynomialTangent

/-! The manuscript's logarithmic polynomial tilt grows at most linearly on
the microscopic latitude scale, so a strict Gaussian gap absorbs it. -/
@[expose] public section
namespace SlowEquilibration.SourcePureLogPolynomialEnvelope
noncomputable section
open Filter Set
open scoped Topology

/-- A uniform bound for the logarithm divided by the square-root width. -/
theorem log_sqrt_uniform_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
    Real.log (n+2 : ℕ)/Real.sqrt (n+2 : ℕ) ≤ K := by
  obtain ⟨K,hK⟩ :=
    SourcePureLogPolynomialTangent.log_div_sqrt_dimension_tendsto_zero.bddAbove_range
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro n
  exact (hK ⟨n,rfl⟩).trans (le_max_left _ _)
/-- A linear tilt is absorbed by an arbitrarily small Gaussian loss. -/
theorem linear_gaussian_absorption {δ D u : ℝ} (hδ : 0 < δ) :
    D*|u| ≤ δ*u^2 + D^2/(4*δ) := by
  have hd : 0 < 4*δ := by positivity
  have h : D*|u| - δ*|u|^2 ≤ D^2/(4*δ) :=
    (le_div_iff₀ hd).mpr (by nlinarith [sq_nonneg (2*δ*|u|-D)])
  rw [sq_abs] at h
  linarith

/-- The exact source perturbation, including its logarithmic centering, is
uniformly at most linear in the scaled latitude `u`. -/
theorem centered_polynomial_linear_bound
    (p n : ℕ) (m t u β cp K : ℝ) (hcp : 0 < cp)
    (hKn : Real.log (n+2 : ℕ)/Real.sqrt (n+2 : ℕ) ≤ K)
    (hm : |m| ≤ 1)
    (hz : |m+u/Real.sqrt (n+2 : ℕ)| ≤ 1) :
    |β*(t-Real.log (n+2 : ℕ)/(2*cp))*
      ((m+u/Real.sqrt (n+2 : ℕ))^p-m^p)| ≤
      (|β| *(|t|+K/(2*cp))*(p:ℝ))*|u| := by
  let s : ℝ := Real.sqrt (n+2 : ℕ)
  let lam : ℝ := Real.log (n+2 : ℕ)/(2*cp)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : 1 ≤ s := by
    dsimp [s]
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ n+2 by omega))
  have hlog : 0 ≤ Real.log (n+2 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n+2 by omega))
  have hlam : 0 ≤ lam := div_nonneg hlog (by positivity)
  have hts : |t| / s ≤ |t| := (div_le_iff₀ hs).mpr (by
    nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hs1)])
  have hls : lam/s ≤ K/(2*cp) := by
    dsimp [lam,s] at *
    rw [show Real.log (n+2 : ℕ)/(2*cp)/Real.sqrt (n+2 : ℕ) =
      (Real.log (n+2 : ℕ)/Real.sqrt (n+2 : ℕ))/(2*cp) by ring]
    exact div_le_div_of_nonneg_right hKn (by positivity)
  have hcoeff : |t-lam|/s ≤ |t|+K/(2*cp) := by
    calc
      _ ≤ (|t|+lam)/s := (div_le_div_of_nonneg_right
        (by calc
          |t-lam| ≤ |t|+|lam| := abs_sub t lam |>.trans_eq (by ring)
          _ = |t|+lam := by rw [abs_of_nonneg hlam]) hs.le)
      _ = |t|/s+lam/s := by ring
      _ ≤ _ := add_le_add hts hls
  have hdist : |(m+u/s)-m| = |u|/s := by
    rw [add_sub_cancel_left, abs_div, abs_of_pos hs]
  have hgap : |(m+u/s)^p-m^p| ≤ (p:ℝ)*|u|/s := by
    calc
      _ ≤ (p:ℝ)*|(m+u/s)-m| :=
        SourcePureLogPolynomialTangent.power_lipschitz_unit p hz hm
      _ = _ := by rw [hdist]; ring
  change |β*(t-lam)*((m+u/s)^p-m^p)| ≤
    (|β| *(|t|+K/(2*cp))*(p:ℝ))*|u|
  rw [abs_mul, abs_mul]
  calc
    |β| *|t-lam| *|(m+u/s)^p-m^p| ≤
        |β| *|t-lam| *((p:ℝ)*|u|/s) := by gcongr
    _ = (|β| *(|t-lam|/s))*((p:ℝ)*|u|) := by ring
    _ ≤ (|β| *(|t|+K/(2*cp)))*((p:ℝ)*|u|) := by gcongr
    _ = _ := by ring

end
end SlowEquilibration.SourcePureLogPolynomialEnvelope
