-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPosteriorLandscapeConcentration

/-! Dimension-scaled bounds for the actual finite-mixture field and every
ambient derivative through order three on the whole physical ball. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourcePosteriorDerivativeConstant {P:ℕ} (c:Degree P→ℝ) (K:ℝ):ℝ:=
  1+∑ p:Degree P,Real.sqrt (c p)*(p.val.val:ℝ)^3*(2*((p.val.val:ℝ)+1)+1+K)

lemma sourcePosteriorDerivativeConstant_pos {P:ℕ} (c:Degree P→ℝ) {K:ℝ} (hK:0 ≤ K) :
    0<sourcePosteriorDerivativeConstant c K:=by
  unfold sourcePosteriorDerivativeConstant
  have hs:0 ≤ ∑ p:Degree P,Real.sqrt (c p)*(p.val.val:ℝ)^3*(2*((p.val.val:ℝ)+1)+1+K):=by
    apply Finset.sum_nonneg
    intro p _
    positivity
  linarith

theorem source_posterior_ordered_derivatives {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (K:ℝ) (J : Disorder N P) (hJ : J ∈ sourcePosteriorOrderedRegularity K)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) (n : ℕ) (hn : n ≤ 3) :
    Real.sqrt (N : ℝ) ^ n * ‖iteratedFDeriv ℝ n (field c J) x‖ ≤
      sourcePosteriorDerivativeConstant c K * (N : ℝ) := by
  have hsum : (∑ p : Degree P, Real.sqrt (c p) *
      (Nat.descFactorial p.val.val n : ℝ) *
      SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)) ≤
      sourcePosteriorDerivativeConstant c K := by
    apply le_trans (b := ∑ p : Degree P,
      Real.sqrt (c p) * (p.val.val : ℝ) ^ 3 * (2*((p.val.val:ℝ)+1)+1+K))
    · apply Finset.sum_le_sum
      intro p hp
      have hfac : (Nat.descFactorial p.val.val n : ℝ) ≤ (p.val.val : ℝ) ^ 3 := by
        exact_mod_cast (Nat.descFactorial_le_pow p.val.val n).trans
          (pow_le_pow_right' (show 1 ≤ p.val.val by omega) hn)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
      · exact hJ p
      · exact SphericalAging.GaussianLandscape.landscapeNorm_nonnegative _ _ _
      · positivity
    · unfold sourcePosteriorDerivativeConstant
      linarith
  exact (field_iteratedFDeriv_ball_bound hN c J x hx n).trans
    ((mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)).trans_eq (by ring))


theorem source_posterior_ordered_ball_bounds {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (K:ℝ) (J : Disorder N P) (hJ : J ∈ sourcePosteriorOrderedRegularity K)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) :
    |field c J x| ≤ sourcePosteriorDerivativeConstant c K * (N : ℝ) ∧
    ‖gradient (field c J) x‖ ≤ sourcePosteriorDerivativeConstant c K * Real.sqrt (N : ℝ) ∧
    ‖iteratedFDeriv ℝ 2 (field c J) x‖ ≤ sourcePosteriorDerivativeConstant c K ∧
    ‖iteratedFDeriv ℝ 3 (field c J) x‖ ≤ sourcePosteriorDerivativeConstant c K / Real.sqrt (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (show 0 < N by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have hzero := source_posterior_ordered_derivatives hN c K J hJ x hx 0 (by norm_num)
  have hone := source_posterior_ordered_derivatives hN c K J hJ x hx 1 (by norm_num)
  have htwo := source_posterior_ordered_derivatives hN c K J hJ x hx 2 (by norm_num)
  have hthree := source_posterior_ordered_derivatives hN c K J hJ x hx 3 (by norm_num)
  have hgrad : ‖gradient (field c J) x‖ = ‖iteratedFDeriv ℝ 1 (field c J) x‖ := by
    rw [gradient, LinearIsometryEquiv.norm_map, norm_iteratedFDeriv_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hzero
  · rw [hgrad]
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ sourcePosteriorDerivativeConstant c K * (N : ℝ) := by simpa only [pow_one] using hone
      _ = Real.sqrt (N : ℝ) * (sourcePosteriorDerivativeConstant c K * Real.sqrt (N : ℝ)) := by
        calc
          _ = sourcePosteriorDerivativeConstant c K * Real.sqrt (N : ℝ) ^ 2 :=
            congrArg (fun z => sourcePosteriorDerivativeConstant c K * z) hsq.symm
          _ = _ := by ring
  · rw [hsq] at htwo
    rw [mul_comm (sourcePosteriorDerivativeConstant c K) (N : ℝ)] at htwo
    exact (mul_le_mul_iff_right₀ hNr).mp htwo
  · apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hNr).mp
    calc
      _ = Real.sqrt (N : ℝ) ^ 3 * ‖iteratedFDeriv ℝ 3 (field c J) x‖ := by
        calc
          _ = Real.sqrt (N : ℝ) ^ 2 *
              (‖iteratedFDeriv ℝ 3 (field c J) x‖ * Real.sqrt (N : ℝ)) :=
            congrArg (fun z => z * (‖iteratedFDeriv ℝ 3 (field c J) x‖ *
              Real.sqrt (N : ℝ))) hsq.symm
          _ = _ := by ring
      _ ≤ sourcePosteriorDerivativeConstant c K * (N : ℝ) := hthree
      _ = _ := by ring


end
end SlowEquilibration.PairConditionalDeterminantMoments
