-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCuspBarrier

@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture.CuspCoordinate
open Set Filter Asymptotics
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {μ : InfiniteMixture} (c : CuspCoordinate μ)

/-- The literal leading coefficient `C_d` in the source trial-pressure barrier. -/
def barrierCoefficient : ℝ :=
  (2 * c.m : ℕ) * μ.qD / (((2 * c.m + 1 : ℕ) : ℝ) * (1 - μ.qD)) *
    c.a ^ (-((2 * c.m : ℕ) : ℝ)⁻¹)

/-- The actual trial-pressure difference at the two constructed roots. -/
def epsilonBarrier (ε : ℝ) : ℝ :=
  μ.cuspTrialPressure (c.epsilonTemperature ε) (c.qPlus ε) -
    μ.cuspTrialPressure (c.epsilonTemperature ε) (c.qMinus ε)

theorem barrierCoefficient_pos : 0 < c.barrierCoefficient := by
  have hi : μ.qD ∈ Ioo (0 : ℝ) 1 := by
    simpa only [c.zero,add_zero] using c.interior 0
      (show (0 : ℝ) ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])
  have hm := c.m_pos
  unfold barrierCoefficient
  exact mul_pos (div_pos (mul_pos (by positivity) hi.1)
    (mul_pos (by positivity) (sub_pos.mpr hi.2))) (Real.rpow_pos_of_pos c.a_pos _)

theorem epsilonBarrier_eq {ε : ℝ} (hε : 0 ≤ ε) :
    c.epsilonBarrier ε = c.trialBarrier (c.rootScale ε) := by
  rw [epsilonBarrier,c.trialBarrier_eq,c.epsilonTemperature_eq hε]
  rfl

private theorem scale_main_term {ε : ℝ} (hε : 0 < ε) :
    ((2 * c.m : ℕ) * c.a * μ.qD / (((2 * c.m + 1 : ℕ) : ℝ) * (1 - μ.qD))) *
      c.rootScale ε ^ (2*c.m+1) =
      c.barrierCoefficient * ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹) := by
  have hh : c.rootScale ε ^ (2*c.m) = ε / c.a :=
    (eq_div_iff c.a_pos.ne').mpr (by simpa only [mul_comm] using c.rootScale_pow hε.le)
  rw [pow_succ,hh,rootScale,Real.div_rpow hε.le c.a_pos.le,
    Real.rpow_add hε,Real.rpow_one,barrierCoefficient,Real.rpow_neg c.a_pos.le]
  field_simp [c.a_pos.ne']

private theorem scale_error_term {ε : ℝ} (hε : 0 < ε) :
    c.rootScale ε ^ (2*c.m+2) =
      (c.a ^ (-(c.m : ℝ)⁻¹) / c.a) * ε ^ (1 + (c.m : ℝ)⁻¹) := by
  have hh : c.rootScale ε ^ (2*c.m) = ε / c.a :=
    (eq_div_iff c.a_pos.ne').mpr (by simpa only [mul_comm] using c.rootScale_pow hε.le)
  rw [pow_add,hh,c.rootScale_sq hε.le,Real.rpow_add hε,Real.rpow_one]
  ring

/-- The full actual source barrier expansion, with explicit coefficient and
next-order power; no barrier asymptotic is supplied as a premise. -/
theorem epsilonBarrier_remainder :
    (fun ε : ℝ => c.epsilonBarrier ε -
      c.barrierCoefficient * ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹))
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ (1 + (c.m : ℝ)⁻¹)) := by
  have hO := c.trialBarrier_remainder.comp_tendsto
    (c.rootScale_tendsto.mono_right nhdsWithin_le_nhds)
  have he : (fun ε : ℝ => c.rootScale ε ^ (2*c.m+2)) =O[𝓝[>] (0 : ℝ)]
      (fun ε => ε ^ (1 + (c.m : ℝ)⁻¹)) := by
    apply ((isBigO_refl (fun ε : ℝ => ε ^ (1 + (c.m : ℝ)⁻¹)) (𝓝[>] (0 : ℝ))).const_mul_left
      (c.a ^ (-(c.m : ℝ)⁻¹) / c.a)).congr' ?_ .rfl
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (c.scale_error_term hε).symm
  apply (hO.trans he).congr' ?_ .rfl
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_def]
  rw [c.scale_main_term hε,← c.epsilonBarrier_eq hε.le]

/-- The source multiplicative form of the trial barrier expansion. -/
theorem epsilonBarrier_relative_remainder :
    (fun ε : ℝ => c.epsilonBarrier ε /
      (c.barrierCoefficient * ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹)) - 1)
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ ((2*c.m : ℕ) : ℝ)⁻¹) := by
  have hO := c.epsilonBarrier_remainder.mul
    (isBigO_refl (fun ε : ℝ => (ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹))⁻¹) (𝓝[>] (0 : ℝ)))
  have hm : (c.m : ℝ) ≠ 0 := by have := c.m_pos; positivity
  have hexp : (1 + (c.m : ℝ)⁻¹) - (1 + ((2*c.m : ℕ) : ℝ)⁻¹) = ((2*c.m : ℕ) : ℝ)⁻¹ := by
    push_cast
    field_simp
    ring
  apply (hO.const_mul_left c.barrierCoefficient⁻¹).congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hn := (Real.rpow_pos_of_pos hε (1 + ((2*c.m : ℕ) : ℝ)⁻¹)).ne'
    have hid (B C t : ℝ) (hC : C ≠ 0) (ht : t ≠ 0) :
        C⁻¹ * ((B - C * t) * t⁻¹) = B / (C * t) - 1 := by
      field_simp
    exact hid _ _ _ c.barrierCoefficient_pos.ne' hn
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    change ε ^ (1 + (c.m : ℝ)⁻¹) * (ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹))⁻¹ = _
    rw [← div_eq_mul_inv,← Real.rpow_sub hε,hexp]

end SlowEquilibration.InfiniteMixture.CuspCoordinate
