-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeLaplace
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! Large-volume Laplace estimates with all actual chart prefactors absorbed
in a fixed pressure tolerance. The dimension thresholds are uniform in the
Hamiltonian, center and overlap region. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem latitude_chart_upper_prefactor_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      4*(latitudeNormalization n).toReal ≤ Real.exp (((n+1 : ℕ) : ℝ)*ε) := by
  have hnorm := latitudeNormalization_log_eventually_le (half_pos hε)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.log 4/((n+1 : ℕ) : ℝ) < ε/2 := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log 4)
    have hlim : Tendsto (fun n : ℕ => Real.log 4/((n+1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Nat.cast_add,Nat.cast_one,mul_zero,div_eq_mul_inv,one_div,one_mul] using ht
    exact hlim.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hnorm,hsmall,eventually_ge_atTop 1] with n hn hs hdim
  have hC : 0 < (latitudeNormalization n).toReal :=
    ENNReal.toReal_pos (latitudeNormalization_pos hdim).ne' (latitudeNormalization_ne_top n)
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  apply (Real.log_le_iff_le_exp (mul_pos (by norm_num) hC)).mp
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hC.ne']
  have hn' : Real.log (latitudeNormalization n).toReal/((n+1 : ℕ) : ℝ) ≤ ε/2 := by
    simpa only [Nat.cast_add,Nat.cast_one] using hn
  have hh : (Real.log 4+Real.log (latitudeNormalization n).toReal)/((n+1 : ℕ) : ℝ) ≤ ε := by
    rw [add_div]
    linarith
  have hh' := (div_le_iff₀ hN).mp hh
  linarith

/-- A literal restricted partition has the desired exponential upper once
its actual latitude profile is bounded. One threshold works for all fields,
centers, Borel overlap sets and numerical profile bounds. -/
theorem partitionOn_eventually_le_of_latitudeProfile_upper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (β : ℝ) (H : Vector (n+1) → ℝ), Continuous H →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (A : Set ℝ), MeasurableSet A →
      ∀ (M : ℝ), (∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → latitudePartitionProfile n β H u q ≤ M) →
      partitionOn β H (overlapRegion u A) ≤ Real.exp (((n+1 : ℕ) : ℝ)*(M+ε)) := by
  filter_upwards [latitude_chart_upper_prefactor_eventually hε,eventually_ge_atTop 2] with n hn hdim
  intro β H hH u hu A hA M hupper
  have hh := partitionOn_le_latitudeProfile_upper hdim β hH u hu hA hupper
  calc
    _ ≤ (4*(latitudeNormalization n).toReal)*Real.exp (((n+1 : ℕ) : ℝ)*M) := hh
    _ ≤ Real.exp (((n+1 : ℕ) : ℝ)*ε)*Real.exp (((n+1 : ℕ) : ℝ)*M) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem latitude_chart_lower_prefactor_eventually {a b ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n+1 : ℕ) : ℝ)*ε) ≤ (latitudeNormalization n).toReal*a*(b-a) := by
  let c : ℝ := (1/4)*a*(b-a)
  have hc : 0 < c := by dsimp [c]; positivity
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log c)
  have hlim : Tendsto (fun n : ℕ => Real.log c/((n+1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_one,mul_zero,div_eq_mul_inv,one_div,one_mul] using ht
  filter_upwards [hlim.eventually (lt_mem_nhds (show -ε < (0 : ℝ) by linarith)),
    eventually_ge_atTop 2] with n hn hdim
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hlog : -((n+1 : ℕ) : ℝ)*ε ≤ Real.log c := by
    have hh := (lt_div_iff₀ hN).mp hn
    linarith
  have hexp : Real.exp (-((n+1 : ℕ) : ℝ)*ε) ≤ c := by
    simpa only [Real.exp_log hc] using Real.exp_le_exp.mpr hlog
  apply hexp.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (latitudeNormalization_toReal_ge_quarter hdim) ha.le)
    (sub_nonneg.mpr hab.le)

/-- A genuine overlap-band lower Laplace bound, with any fixed nonzero radial
subinterval and no prefactor remaining in the resulting exponential. -/
theorem partitionOn_eventually_ge_of_latitudeProfile_lower {a b ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 2) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (β : ℝ) (H : Vector (n+1) → ℝ), Continuous H →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (A : Set ℝ), MeasurableSet A →
      (∀ r ∈ Icc a b, radialLatitude r ∈ A) → ∀ (M : ℝ),
      (∀ r ∈ Icc a b, M ≤ latitudePartitionProfile n β H u (radialLatitude r)) →
      Real.exp (((n+1 : ℕ) : ℝ)*(M-ε)) ≤ partitionOn β H (overlapRegion u A) := by
  filter_upwards [latitude_chart_lower_prefactor_eventually ha hab hε,eventually_ge_atTop 2] with n hn hdim
  intro β H hH u hu A hA hband M hlower
  have hh := partitionOn_ge_latitudeProfile_lower hdim β hH u hu hA ha hab.le hb hband hlower
  calc
    _ = Real.exp (-((n+1 : ℕ) : ℝ)*ε)*Real.exp (((n+1 : ℕ) : ℝ)*M) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ ((latitudeNormalization n).toReal*a*(b-a))*Real.exp (((n+1 : ℕ) : ℝ)*M) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ ≤ _ := hh

theorem coreBand_eq_overlapRegion {N : ℕ} (u : Vector N) (q w : ℝ) :
    coreBand u q w = overlapRegion u (Icc (q-w) (q+w)) := by
  ext x
  change |overlap x u-q| ≤ w ↔ overlap x u ∈ Icc (q-w) (q+w)
  rw [abs_le]
  constructor <;> rintro ⟨hlo,hhi⟩ <;> constructor <;> linarith

def coreRadialLower (q w : ℝ) : ℝ := Real.sqrt (2*(1-q-w))
def coreRadialUpper (q w : ℝ) : ℝ := Real.sqrt (2*(1-q+w))

theorem coreRadialInterval {q w : ℝ} (hw : 0 < w)
    (hlo : -1 < q-w) (hhi : q+w < 1) :
    0 < coreRadialLower q w ∧ coreRadialLower q w < coreRadialUpper q w ∧
      coreRadialUpper q w < 2 ∧
      ∀ r ∈ Icc (coreRadialLower q w) (coreRadialUpper q w),
        radialLatitude r ∈ Icc (q-w) (q+w) := by
  have ha : 0 < 2*(1-q-w) := by linarith
  have hb : 0 < 2*(1-q+w) := by linarith
  have hlow : 0 < coreRadialLower q w := Real.sqrt_pos.mpr ha
  have hlowsq : (coreRadialLower q w)^2=2*(1-q-w) := Real.sq_sqrt ha.le
  have huppsq : (coreRadialUpper q w)^2=2*(1-q+w) := Real.sq_sqrt hb.le
  have hupp : 0 ≤ coreRadialUpper q w := Real.sqrt_nonneg _
  have hlt : coreRadialLower q w < coreRadialUpper q w := by nlinarith
  have htwo : coreRadialUpper q w < 2 := by nlinarith
  refine ⟨hlow,hlt,htwo,?_⟩
  intro r hr
  have hr0 : 0 ≤ r := hlow.le.trans hr.1
  have hsqlo : (coreRadialLower q w)^2 ≤ r^2 := (sq_le_sq₀ hlow.le hr0).mpr hr.1
  have hsqhi : r^2 ≤ (coreRadialUpper q w)^2 := (sq_le_sq₀ hr0 hupp).mpr hr.2
  unfold radialLatitude
  constructor <;> nlinarith

/-- The actual core-band lower, on a literal fixed-width band. The dimension
threshold depends only on the band and pressure tolerance, not on the field
or the spherical reference point. -/
theorem coreBand_partition_eventually_ge {q w ε : ℝ} (hw : 0 < w)
    (hlo : -1 < q-w) (hhi : q+w < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (β : ℝ) (H : Vector (n+1) → ℝ), Continuous H →
      ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (M : ℝ),
      (∀ r ∈ Icc (q-w) (q+w), M ≤ latitudePartitionProfile n β H u r) →
      Real.exp (((n+1 : ℕ) : ℝ)*(M-ε)) ≤ partitionOn β H (coreBand u q w) := by
  obtain ⟨ha,hab,hb,hband⟩ := coreRadialInterval hw hlo hhi
  filter_upwards [partitionOn_eventually_ge_of_latitudeProfile_lower ha hab hb hε] with n hn
  intro β H hH u hu M hlower
  rw [coreBand_eq_overlapRegion]
  exact hn β H hH u hu _ measurableSet_Icc hband M (fun r hr => hlower _ (hband r hr))

end
end SlowEquilibration.SphericalModel
