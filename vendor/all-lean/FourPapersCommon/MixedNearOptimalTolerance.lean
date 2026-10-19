module
public import FourPapersCommon.MixedLocalLeftUniform
public import FourPapersCommon.MixtureCoercivity

@[expose] public section

/-! A covariance-only near-optimality tolerance.  The local instability
estimate and the far-interval tangent remainder can be made effective
simultaneously, independently of the depth, masses, field, and system size. -/
noncomputable section
open Real Set
open SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 600000

theorem exists_mixed_nearOptimal_tolerance (ξ : AdmissibleEvenMixture)
    {t₀ : ℝ} (ht₀ : t₀ < 1) :
    ∃ ε > (0 : ℝ), ε ≤ 1 ∧
      mixedLocalLeftConstant ξ * ε ^ (1 / 6 : ℝ) ≤ 1 - t₀ ∧
      ∀ u ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1,
        (1 - t₀) / mixedLocalLeftConstant ξ ≤ |u - q| →
        2 * section4OptimalityBound (mixedBeta ξ) * Real.sqrt ε <
          (1 - t₀) * ξ.tangentRemainder u q := by
  have hC := mixedLocalLeftConstant_pos ξ
  have hT : 0 < 1 - t₀ := sub_pos.mpr ht₀
  have hB := section4OptimalityBound_pos (mixedBeta ξ)
  obtain ⟨c, hc, Hc⟩ := ξ.tangentRemainder_uniform_away (div_pos hT hC)
  let A := (1 - t₀) / (2 * mixedLocalLeftConstant ξ)
  let B := (1 - t₀) * c / (4 * section4OptimalityBound (mixedBeta ξ))
  have hA : 0 < A := div_pos hT (mul_pos (by norm_num) hC)
  have hBp : 0 < B := div_pos (mul_pos hT hc) (mul_pos (by norm_num) hB)
  let ε := min (1 : ℝ) (min (A ^ 6) (B ^ 2))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (pow_pos hA _) (pow_pos hBp _))
  have hεA : ε ≤ A ^ 6 := (min_le_right _ _).trans (min_le_left _ _)
  have hεB : ε ≤ B ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hrpow : ε ^ (1 / 6 : ℝ) ≤ A := by
    have H := Real.rpow_le_rpow hε.le hεA (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have HA := Real.pow_rpow_inv_natCast hA.le (by norm_num : (6 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat, inv_eq_one_div] at HA
    exact H.trans_eq HA
  have hsqrt : Real.sqrt ε ≤ B := by
    exact (Real.sqrt_le_sqrt hεB).trans_eq (Real.sqrt_sq hBp.le)
  have hCA : mixedLocalLeftConstant ξ * A = (1 - t₀) / 2 := by
    dsimp [A]
    field_simp
  have hBB : 2 * section4OptimalityBound (mixedBeta ξ) * B = (1 - t₀) * c / 2 := by
    dsimp [B]
    field_simp
    norm_num
  refine ⟨ε, hε, min_le_left _ _, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left hrpow hC.le
    rw [hCA] at H
    linarith
  · intro u hu q hq haway
    have Hc' := Hc u ⟨by linarith [hu.1], hu.2⟩ q ⟨by linarith [hq.1], hq.2⟩ haway
    have Hsqrt := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB.le)
    rw [hBB] at Hsqrt
    have Hrem := mul_le_mul_of_nonneg_left Hc' hT.le
    nlinarith only [Hsqrt, Hrem, mul_pos hT hc]

end FourPapersCommon
