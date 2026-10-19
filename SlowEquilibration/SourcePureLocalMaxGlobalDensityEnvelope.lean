-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureTruncatedLocalMaxDensity

/-! A source-wide exponential upper envelope for the *actual* pure
negative-Hessian local-maximum intensity in a compact exterior mark band.
The decay is measured in the physical, unnormalized energy coordinate. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open scoped ENNReal Topology
set_option maxHeartbeats 500000

/-- The true mark-truncated density has the source contact slope on the
whole compact exterior mark band, not merely on a logarithmic window. -/
theorem sourcePure_truncatedLocalMax_global_upper
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ} (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ H : ℝ,
      pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) H ≤
      C*Real.exp (-(β*x)*(H-(n+2 : ℕ)*E))/Real.sqrt (n+2 : ℕ) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  obtain ⟨c,C,hc,hC,hPref⟩ := pure_localMax_physical_prefactors
    p hp a ha h.overlap_range.1 (Z := Z) hg
  refine ⟨C,hC,?_⟩
  filter_upwards [hPref] with n hn
  intro H
  let N : ℝ := (n+2 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  by_cases hH : H ∈ Ioo (N*l) (N*r)
  · let e := H/N
    have he : e ∈ Ioo l r := by
      dsimp [e] at *
      constructor
      · apply (lt_div_iff₀ hN).mpr
        nlinarith [hH.1]
      · apply (div_lt_iff₀ hN).mpr
        nlinarith [hH.2]
    have heMark : (p : ℝ)*e ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z := by
      constructor
      · have hm := mul_le_mul_of_nonneg_left he.1.le hp0.le
        dsimp [μ] at *
        linarith
      · have hm := mul_le_mul_of_nonneg_left he.2.le hp0.le
        linarith
    have hHEq : H = N*e := by dsimp [e]; field_simp
    have hPrefUpper := (hn e heMark).2.1.trans (hn e heMark).2.2
    rw [← hHEq] at hPrefUpper
    have hUpper : (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal ≤
        C*(Real.sqrt N)⁻¹*Real.exp (N*pureMarkedComplexity p hp a ha Q e) := by
      have hh := ENNReal.toReal_mono (by simp) hPrefUpper
      change _ ≤ (ENNReal.ofReal
        (C*(Real.sqrt N)⁻¹*Real.exp (N*pureMarkedComplexity p hp a ha Q e))).toReal at hh
      rw [ENNReal.toReal_ofReal (by positivity)] at hh
      exact hh
    have hLoss := sourcePureMarkedComplexity_global_linear_loss p hp a ha h e
    have hExponent : N*pureMarkedComplexity p hp a ha Q e ≤ -(β*x)*(H-N*E) := by
      have hs := mul_le_mul_of_nonneg_left hLoss hN.le
      dsimp [E, μ] at *
      nlinarith [hHEq]
    have hExp := Real.exp_le_exp.mpr hExponent
    have hMul := mul_le_mul_of_nonneg_left hExp
      (by positivity : 0 ≤ C*(Real.sqrt N)⁻¹)
    calc
      pureTruncatedLocalMaxDensity n p hp a ha Q (N*l) (N*r) H =
          (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal := by
            simp [pureTruncatedLocalMaxDensity,hH]
      _ ≤ C*(Real.sqrt N)⁻¹*Real.exp (N*pureMarkedComplexity p hp a ha Q e) := hUpper
      _ ≤ C*Real.exp (-(β*x)*(H-N*E))/Real.sqrt N := by
        convert hMul using 1
        simp only [div_eq_mul_inv]
        ring
  · calc
      pureTruncatedLocalMaxDensity n p hp a ha Q (N*l) (N*r) H = 0 := by
        simp [pureTruncatedLocalMaxDensity,hH]
      _ ≤ C*Real.exp (-(β*x)*(H-N*E))/Real.sqrt N := by positivity

end SlowEquilibration.SphericalMarkedWindows
