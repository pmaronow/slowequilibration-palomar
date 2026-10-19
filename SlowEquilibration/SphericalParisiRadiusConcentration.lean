-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiCavityReference
public import SphericalAging.GaussianRadiusVariance
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Concentration of the literal generating Gaussian bulk radius. This
supplies a genuine probability estimate for the independent radius factor
in the spherical cavity reference product, without a shell-concentration
premise. -/

namespace SlowEquilibration.SphericalParisiRadiusConcentration

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalParisiCavityReference
open SphericalAging.SphereInitialLaw SphericalAging.GaussianRadiusVariance
open scoped Topology InnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite quantitative bound for the actual relative squared radius. -/
theorem actual_gaussian_relative_radius_bound {N : ℕ} (hN : 1 ≤ N)
    {ε : ℝ} (hε : 0 < ε) :
    (gaussianLaw N).real {g : Vector N | ε ≤ |‖g‖^2/(N : ℝ)-1|} ≤
      (Real.pi^2/2)/(ε^2*(N : ℝ)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let X : Vector N → ℝ := fun g => (‖g‖^2-(N : ℝ))^2
  have hi : Integrable X (gaussianLaw N) := by
    exact ((memLp_norm_sq (E := Vector N)).sub (memLp_const (N : ℝ))).integrable_sq
  have hm := mul_meas_ge_le_integral_of_nonneg
    (.of_forall (fun g : Vector N => sq_nonneg (‖g‖^2-(N : ℝ)))) hi ((ε*(N : ℝ))^2)
  have hs : {g : Vector N | ε ≤ |‖g‖^2/(N : ℝ)-1|} ⊆
      {g : Vector N | (ε*(N : ℝ))^2 ≤ X g} := by
    intro g hg
    change ε ≤ |‖g‖^2/(N : ℝ)-1| at hg
    change (ε*(N : ℝ))^2 ≤ X g
    have he : ‖g‖^2/(N : ℝ)-1=(‖g‖^2-(N : ℝ))/(N : ℝ) := by
      field_simp
    rw [he, abs_div, abs_of_pos hn] at hg
    have ha := (le_div_iff₀ hn).mp hg
    have hh := (sq_le_sq₀ (mul_nonneg hε.le hn.le) (abs_nonneg _)).mpr ha
    simpa only [sq_abs] using hh
  have hv : (∫ g : Vector N, X g ∂gaussianLaw N) =
      variance (fun g : Vector N => ‖g‖^2) (gaussianLaw N) := by
    change (∫ g : Vector N,X g ∂stdGaussian (Vector N))=
      variance (fun g : Vector N => ‖g‖^2) (stdGaussian (Vector N))
    rw [variance_eq_integral (by fun_prop), integral_norm_sq]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rfl
  rw [hv] at hm
  have hm' := mul_le_mul_of_nonneg_left
    (measureReal_mono (μ := gaussianLaw N) hs (measure_ne_top _ _))
    (sq_nonneg (ε*(N : ℝ)))
  have hvar := radius_variance_le (E := Vector N)
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hvar
  have ht := (hm'.trans hm).trans hvar
  have ha : 0 < (ε*(N : ℝ))^2 := sq_pos_of_pos (mul_pos hε hn)
  have hd : (gaussianLaw N).real {g : Vector N | ε ≤ |‖g‖^2/(N : ℝ)-1|} ≤
      ((Real.pi^2/2)*(N : ℝ))/(ε*(N : ℝ))^2 := by
    apply (le_div_iff₀ ha).mpr
    nlinarith [ht]
  refine hd.trans_eq ?_
  field_simp

/-- The exact pushforward radius law satisfies the same bound. -/
theorem actual_radius_law_bound {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    (radiusLaw N).real {r : ℝ | ε ≤ |r^2/(N : ℝ)-1|} ≤
      (Real.pi^2/2)/(ε^2*(N : ℝ)) := by
  rw [radiusLaw, map_measureReal_apply measurable_norm (by measurability)]
  exact actual_gaussian_relative_radius_bound hN hε

/-- The actual relative Gaussian radius converges in probability to one. -/
theorem actual_radius_concentration {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => (radiusLaw N).real {r : ℝ | ε ≤ |r^2/(N : ℝ)-1|})
      atTop (𝓝 (0 : ℝ)) := by
  have hlim : Tendsto (fun N : ℕ => (Real.pi^2/2)/(ε^2*(N : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    have he : (fun N : ℕ => (Real.pi^2/2)/(ε^2*(N : ℝ)))=
        (fun N : ℕ => ((Real.pi^2/2)/(ε^2))*(1/(N : ℝ))) := by
      funext N
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he]
    convert tendsto_one_div_atTop_nhds_zero_nat.const_mul ((Real.pi^2/2)/(ε^2)) using 1
    norm_num
  refine squeeze_zero' (.of_forall (fun _ => measureReal_nonneg)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact actual_radius_law_bound hN hε

/-- The independent radius factor in the literal cavity reference law is
good with probability tending to one, for every fixed relative tolerance. -/
theorem actual_good_radius_probability {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => (radiusLaw N).real {r : ℝ | |r^2/(N : ℝ)-1| < ε})
      atTop (𝓝 (1 : ℝ)) := by
  have he (N : ℕ) :
      (radiusLaw N).real {r : ℝ | |r^2/(N : ℝ)-1| < ε} =
        1-(radiusLaw N).real {r : ℝ | ε ≤ |r^2/(N : ℝ)-1|} := by
    have hs : {r : ℝ | |r^2/(N : ℝ)-1| < ε} =
        {r : ℝ | ε ≤ |r^2/(N : ℝ)-1|}ᶜ := by ext r; simp
    rw [hs, measureReal_compl (by measurability)]
    simp
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub (actual_radius_concentration hε)

end
end SlowEquilibration.SphericalParisiRadiusConcentration
