-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCuspRoots

@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture.CuspCoordinate
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {μ : InfiniteMixture} (c : CuspCoordinate μ)

/-- The literal positive root scale in the source expansion. -/
def rootScale (ε : ℝ) : ℝ := (ε / c.a) ^ ((2 * c.m : ℕ) : ℝ)⁻¹

def qMinus (ε : ℝ) : ℝ := c.leftRoot (c.rootScale ε)
def qPlus (ε : ℝ) : ℝ := c.rightRoot (c.rootScale ε)

def epsilonTemperature (_c : CuspCoordinate μ) (ε : ℝ) : ℝ :=
  Thresholds.dynamicalThreshold μ.xi * Real.sqrt (1 + ε)

theorem rootScale_pos {ε : ℝ} (hε : 0 < ε) : 0 < c.rootScale ε :=
  Real.rpow_pos_of_pos (div_pos hε c.a_pos) _

theorem rootScale_pow {ε : ℝ} (hε : 0 ≤ ε) :
    c.a * c.rootScale ε ^ (2 * c.m) = ε := by
  rw [rootScale, Real.rpow_inv_natCast_pow (div_nonneg hε c.a_pos.le)
    (by have := c.m_pos; omega)]
  field_simp [c.a_pos.ne']

theorem rootScale_tendsto : Tendsto c.rootScale (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hp : 0 < ((2 * c.m : ℕ) : ℝ)⁻¹ := by
      have := c.m_pos
      positivity
    have ht : Tendsto (fun ε : ℝ => ε / c.a) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds
        ((continuous_id.div_const c.a).tendsto (0 : ℝ)))
    exact ht.rpow_const_nhds_zero hp
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact c.rootScale_pos hε

theorem epsilonTemperature_eq {ε : ℝ} (hε : 0 ≤ ε) :
    c.epsilonTemperature ε = c.temperature (c.rootScale ε) := by
  rw [epsilonTemperature, temperature, c.rootScale_pow hε]

/-- The constructed roots are actual level roots and the larger one is the
literal supremum defining `qStar`. -/
theorem epsilon_roots_eventually :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c.qMinus ε < μ.qD ∧ μ.qD < c.qPlus ε ∧
      c.qMinus ε ∈ Ioo (0 : ℝ) 1 ∧ c.qPlus ε ∈ Ioo (0 : ℝ) 1 ∧
      μ.A (c.qMinus ε) = μ.Amax / (1 + ε) ∧
      μ.A (c.qPlus ε) = μ.Amax / (1 + ε) ∧
      Thresholds.qStar μ.xi (c.epsilonTemperature ε) = c.qPlus ε := by
  have hr := c.rootScale_tendsto (eventually_nhdsWithin_of_eventually_nhds
    (Iio_mem_nhds c.radius_pos))
  have hs := c.rootScale_tendsto c.qStar_eq_rightRoot_eventually
  filter_upwards [self_mem_nhdsWithin,hr,hs] with ε hε hr hs
  have hh := c.rootScale_pos hε
  have hi := c.roots_interior hh.le hr.le
  have hl := c.roots_level hh.le hr.le
  rw [c.rootScale_pow hε.le] at hl
  exact ⟨c.left_lt_qD hh hr.le,c.qD_lt_right hh hr.le,hi.1,hi.2,
    hl.1,hl.2,by rw [c.epsilonTemperature_eq hε.le]; exact hs⟩

theorem rootScale_sq {ε : ℝ} (hε : 0 ≤ ε) :
    c.rootScale ε ^ 2 = c.a ^ (-(c.m : ℝ)⁻¹) * ε ^ (c.m : ℝ)⁻¹ := by
  have hm : (c.m : ℝ) ≠ 0 := by have := c.m_pos; positivity
  rw [rootScale, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hε c.a_pos.le)]
  have he : ((2 * c.m : ℕ) : ℝ)⁻¹ * (2 : ℕ) = (c.m : ℝ)⁻¹ := by
    push_cast
    field_simp
  rw [he, Real.div_rpow hε c.a_pos.le, Real.rpow_neg c.a_pos.le]
  ring

private theorem rootScale_sq_isBigO :
    (fun ε : ℝ => c.rootScale ε ^ 2) =O[𝓝[>] (0 : ℝ)]
      (fun ε => ε ^ (c.m : ℝ)⁻¹) := by
  apply ((Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ (c.m : ℝ)⁻¹)
    (𝓝[>] (0 : ℝ))).const_mul_left (c.a ^ (-(c.m : ℝ)⁻¹))).congr' ?_ .rfl
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (c.rootScale_sq hε.le).symm

/-- The source left root expansion, with the actual `ε^(1/m)` remainder. -/
theorem qMinus_remainder :
    (fun ε : ℝ => c.qMinus ε - (μ.qD - (ε / c.a) ^ ((2 * c.m : ℕ) : ℝ)⁻¹))
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ (c.m : ℝ)⁻¹) := by
  exact (c.leftRoot_remainder.comp_tendsto
    (c.rootScale_tendsto.mono_right nhdsWithin_le_nhds)).trans c.rootScale_sq_isBigO

/-- The source right root expansion, with the actual `ε^(1/m)` remainder. -/
theorem qPlus_remainder :
    (fun ε : ℝ => c.qPlus ε - (μ.qD + (ε / c.a) ^ ((2 * c.m : ℕ) : ℝ)⁻¹))
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ (c.m : ℝ)⁻¹) := by
  exact (c.rightRoot_remainder.comp_tendsto
    (c.rootScale_tendsto.mono_right nhdsWithin_le_nhds)).trans c.rootScale_sq_isBigO

/-- The literal source supremum has the proved right-root expansion. -/
theorem qStar_epsilon_remainder :
    (fun ε : ℝ => Thresholds.qStar μ.xi (c.epsilonTemperature ε) -
      (μ.qD + (ε / c.a) ^ ((2 * c.m : ℕ) : ℝ)⁻¹))
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ (c.m : ℝ)⁻¹) := by
  apply c.qPlus_remainder.congr' ?_ .rfl
  filter_upwards [c.epsilon_roots_eventually] with ε hε
  rw [hε.2.2.2.2.2.2]

end SlowEquilibration.InfiniteMixture.CuspCoordinate
