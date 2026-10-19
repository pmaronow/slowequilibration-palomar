-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianVectorAffineMoments
public import SlowEquilibration.BorderMomentTransfer

/-! All integer moments of the literal border factor on its original space. -/
@[expose] public section
namespace SlowEquilibration.BorderFactorIntegerMoments
noncomputable section
open MeasureTheory ProbabilityTheory GaussianVectorPolynomialMoments
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure Ω}

def factor (k ρ : ℝ) (a : Ω → ℝ) (u : Ω → E) (x : Ω) : ℝ :=
  |k-a x|+‖u x‖^2/ρ

lemma factor_nonneg (k : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (a : Ω → ℝ) (u : Ω → E) (x : Ω) :
    0 ≤ factor k ρ a u x := add_nonneg (abs_nonneg _) (div_nonneg (sq_nonneg _) hρ.le)

lemma factor_measurable (k ρ : ℝ) {a : Ω → ℝ} {u : Ω → E}
    (ha : Measurable a) (hu : Measurable u) : Measurable (factor k ρ a u) :=
  (measurable_const.sub ha).abs.add ((hu.norm.pow_const 2).div_const ρ)

/-- A bound valid at every integer order, including order zero. -/
lemma factor_power_bound (k a : ℝ) (u : E) (r : ℕ) {ρ L : ℝ}
    (hρ : 0 < ρ) (hL : ρ⁻¹ ≤ L) :
    (|k-a|+‖u‖^2/ρ)^r ≤
      (2:ℝ)^(2*r)*(|k|^r+|a|^r)+(2:ℝ)^r*L^r*‖u‖^(2*r) := by
  have ha : |k-a|^r ≤ (2:ℝ)^r*(|k|^r+|a|^r) := by
    simpa only [Real.norm_eq_abs,norm_neg,sub_eq_add_neg] using norm_add_power_le k (-a) r
  have hu : (‖u‖^2/ρ)^r ≤ L^r*‖u‖^(2*r) := by
    have hLp:=pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) hL r
    calc
      _=ρ⁻¹^r*‖u‖^(2*r) := by rw [div_eq_mul_inv,mul_pow,← pow_mul];ring
      _ ≤ _:=mul_le_mul_of_nonneg_right hLp (pow_nonneg (norm_nonneg _) _)
  have hs : (|k-a|+‖u‖^2/ρ)^r ≤ (2:ℝ)^r*(|k-a|^r+(‖u‖^2/ρ)^r) := by
    have hh := norm_add_power_le (|k-a|) (‖u‖^2/ρ) r
    simp only [Real.norm_eq_abs] at hh
    rw [abs_of_nonneg (add_nonneg (abs_nonneg (k-a)) (div_nonneg (sq_nonneg ‖u‖) hρ.le)),
      abs_of_nonneg (abs_nonneg (k-a)),abs_of_nonneg (div_nonneg (sq_nonneg ‖u‖) hρ.le)] at hh
    exact hh
  calc
    _ ≤ (2:ℝ)^r*(|k-a|^r+(‖u‖^2/ρ)^r):=hs
    _ ≤ (2:ℝ)^r*((2:ℝ)^r*(|k|^r+|a|^r)+L^r*‖u‖^(2*r)) := by gcongr
    _=_ := by rw [pow_mul];ring

theorem factor_integer_moment [IsProbabilityMeasure μ]
    (k : ℝ) (r : ℕ) {ρ L Ca Cu : ℝ} (hρ : 0 < ρ) (hL : ρ⁻¹ ≤ L)
    (a : Ω → ℝ) (u : Ω → E) (ha : Measurable a) (hu : Measurable u)
    (haI : Integrable (fun x=>|a x|^r) μ) (huI : Integrable (fun x=>‖u x‖^(2*r)) μ)
    (haM : (∫ x,|a x|^r ∂μ) ≤ Ca) (huM : (∫ x,‖u x‖^(2*r) ∂μ) ≤ Cu) :
    Integrable (fun x=>factor k ρ a u x^r) μ ∧
      (∫ x,factor k ρ a u x^r ∂μ) ≤
        (2:ℝ)^(2*r)*(|k|^r+Ca)+(2:ℝ)^r*L^r*Cu := by
  have hmajor : Integrable (fun x=>(2:ℝ)^(2*r)*(|k|^r+|a x|^r)+
      (2:ℝ)^r*L^r*‖u x‖^(2*r)) μ :=
    ((integrable_const (|k|^r)).add haI).const_mul _ |>.add (huI.const_mul _)
  have hp (x) : factor k ρ a u x^r ≤
      (2:ℝ)^(2*r)*(|k|^r+|a x|^r)+(2:ℝ)^r*L^r*‖u x‖^(2*r) :=
    factor_power_bound k (a x) (u x) r hρ hL
  have hi : Integrable (fun x=>factor k ρ a u x^r) μ :=
    hmajor.mono' ((factor_measurable k ρ ha hu).pow_const r).aestronglyMeasurable
      (ae_of_all μ (fun x=>by rw [Real.norm_of_nonneg (pow_nonneg (factor_nonneg k hρ a u x) _)];exact hp x))
  refine ⟨hi,(integral_mono hi hmajor hp).trans ?_⟩
  have hsum := integral_add
    (((integrable_const (|k|^r)).add haI).const_mul ((2:ℝ)^(2*r)))
    (huI.const_mul ((2:ℝ)^r*L^r))
  simp only [Pi.add_apply] at hsum
  rw [hsum,integral_const_mul,integral_const_mul,integral_add (integrable_const _) haI,
    integral_const,probReal_univ,one_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl haM) (by positivity))
    (mul_le_mul_of_nonneg_left huM (by have hL0:0≤L:=(inv_nonneg.mpr hρ.le).trans hL; positivity))

end
end SlowEquilibration.BorderFactorIntegerMoments
