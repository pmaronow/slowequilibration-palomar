-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCoarea
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The genuine spherical latitude normalization

The coarea normalization is computed from ordinary angular volume, and its
Gamma ratio is bounded using the proved log-convexity of Euler's Gamma
function. Thus its size is controlled independently of any pressure estimate.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter Metric
open SphereChartVolume SphereVolume
open scoped Topology ENNReal

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem angular_volume_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] :
    (volume : Measure E).toSphere.real univ =
      2*(Real.sqrt Real.pi)^Module.finrank ℝ E/Real.Gamma ((Module.finrank ℝ E : ℝ)/2) := by
  have hd : 0 < (Module.finrank ℝ E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hg : Real.Gamma ((Module.finrank ℝ E : ℝ)/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [Measure.toSphere_real_apply_univ]
  unfold Measure.real
  rw [InnerProductSpace.volume_ball]
  simp only [ENNReal.ofReal_one,one_pow,one_mul]
  rw [ENNReal.toReal_ofReal (by positivity),Real.Gamma_add_one (by positivity)]
  field_simp

def latitudeNormalization (n : ℕ) : ℝ≥0∞ :=
  ((volume : Measure (WithLp 2 (Vector n × ℝ))).toSphere univ)⁻¹ *
    (volume : Measure (Vector n)).toSphere univ

theorem latitudeNormalization_ne_top (n : ℕ) : latitudeNormalization n ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · exact ENNReal.inv_ne_top.mpr (SphereVolume.angular_total_ne_zero (E := WithLp 2 (Vector n × ℝ)))
  · exact measure_ne_top _ _

theorem latitudeNormalization_pos {n : ℕ} (hn : 1 ≤ n) : 0 < latitudeNormalization n := by
  let : NeZero n := ⟨by omega⟩
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top ((volume : Measure (WithLp 2 (Vector n × ℝ))).toSphere) univ)
  · exact SphereVolume.angular_total_ne_zero (E := Vector n)

/-- The exact Gamma-ratio normalization of the proved spherical coarea law. -/
theorem latitudeNormalization_toReal {n : ℕ} (hn : 1 ≤ n) :
    (latitudeNormalization n).toReal =
      Real.Gamma (((n+1 : ℕ) : ℝ)/2)/(Real.sqrt Real.pi*Real.Gamma ((n : ℝ)/2)) := by
  let : NeZero n := ⟨by omega⟩
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hg : Real.Gamma ((n : ℝ)/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hg' : Real.Gamma (((n+1 : ℕ) : ℝ)/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold latitudeNormalization
  rw [ENNReal.toReal_mul,ENNReal.toReal_inv]
  change ((volume : Measure (WithLp 2 (Vector n × ℝ))).toSphere.real univ)⁻¹ *
    (volume : Measure (Vector n)).toSphere.real univ = _
  rw [angular_volume_real,angular_volume_real,chartAmbient_finrank]
  rw [show Module.finrank ℝ (Vector n)=n from by simp [Vector,SphericalAging.FiniteModel.Vector],pow_succ]
  field_simp

/-- Euler's actual Gamma function satisfies the required half-step ratio
bound, by its proved log-convexity. -/
theorem gamma_half_ratio_le_sqrt {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x+1/2) ≤ Real.sqrt x*Real.Gamma x := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    hx (show 0 < x+1 by linarith) (show (0 : ℝ)<1/2 by norm_num)
    (show (0 : ℝ)<1/2 by norm_num) (show (1/2 : ℝ)+1/2=1 by norm_num)
  have he : (1/2 : ℝ)*x+(1/2)*(x+1)=x+1/2 := by ring
  rw [he,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,Real.Gamma_add_one hx.ne',Real.sqrt_mul hx.le] at h
  have hg := (Real.Gamma_pos_of_pos hx).le
  have hm : Real.sqrt (Real.Gamma x)*(Real.sqrt x*Real.sqrt (Real.Gamma x)) =
      Real.sqrt x*Real.Gamma x := by
    calc
      _ = Real.sqrt x*(Real.sqrt (Real.Gamma x))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hg]
  rwa [hm] at h

/-- The actual coarea normalizer has only polynomial size. -/
theorem latitudeNormalization_toReal_le_sqrt {n : ℕ} (hn : 1 ≤ n) :
    (latitudeNormalization n).toReal ≤ Real.sqrt (n : ℝ) := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hg := Real.Gamma_pos_of_pos (show 0 < (n : ℝ)/2 by positivity)
  have hp : 1 ≤ Real.sqrt Real.pi := by
    nlinarith [Real.pi_gt_three,Real.sq_sqrt Real.pi_pos.le,Real.sqrt_nonneg Real.pi]
  rw [latitudeNormalization_toReal hn]
  apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hg)).mpr
  have h := gamma_half_ratio_le_sqrt (show 0 < (n : ℝ)/2 by positivity)
  have he : (n : ℝ)/2+1/2=((n+1 : ℕ) : ℝ)/2 := by push_cast; ring
  rw [he] at h
  calc
    _ ≤ Real.sqrt ((n : ℝ)/2)*Real.Gamma ((n : ℝ)/2) := h
    _ ≤ Real.sqrt (n : ℝ)*Real.Gamma ((n : ℝ)/2) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hg.le
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hp (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hg.le)
      nlinarith

/-- The true coarea normalization contributes sublinear logarithmic cost.
This one-sided form suffices in the pressure upper bounds. -/
theorem latitudeNormalization_log_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (latitudeNormalization n).toReal / ((n : ℝ)+1) ≤ ε := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ) / ((n : ℝ)+1)) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext n
    simp
  filter_upwards [eventually_ge_atTop 1, ht.eventually (gt_mem_nhds hε)] with n hn ht'
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 < (latitudeNormalization n).toReal :=
    ENNReal.toReal_pos (latitudeNormalization_pos hn).ne' (latitudeNormalization_ne_top n)
  have hl : Real.log (latitudeNormalization n).toReal ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log hc
    apply (latitudeNormalization_toReal_le_sqrt hn).trans
    have hh : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.sq_sqrt hn'.le,Real.sqrt_nonneg (n : ℝ)]
  exact ((div_le_div_of_nonneg_right hl (by positivity)).trans ht'.le)

end SlowEquilibration.SphericalModel
