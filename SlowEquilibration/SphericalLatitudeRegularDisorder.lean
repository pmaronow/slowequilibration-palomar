-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeMaximumExclusion
public import SlowEquilibration.SphericalLatitudeRegularity
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Uniform latitude continuity on the actual exponentially likely tensor
regularity event, with a modulus proportional to the physical dimension. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Metric InnerProductSpace
open SlowEquilibration.SphericalModel
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem regularDisorder_latitude_field_modulus {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (hJ : J ∈ regularDisorder)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q r : ℝ} (hq : |q| ≤ 1) (hr : |r| ≤ 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    |latitudeField c J w e q y-latitudeField c J w e r y| ≤
      2*derivativeConstant c*((n+2 : ℕ) : ℝ)*Real.sqrt |q-r| := by
  have hball (s : ℝ) (hs : |s| ≤ 1) : latitudeMap w e s y ∈ closedBall 0 (Real.sqrt ((n+2 : ℕ) : ℝ)) := by
    rw [mem_closedBall, dist_zero_right]
    have hnorm := latitudeMap_norm_sq (by omega) w hw e he hs y hy
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hgrad (x : Vector (n+2)) (hx : x ∈ closedBall 0 (Real.sqrt ((n+2 : ℕ) : ℝ))) :
      ‖fderiv ℝ (field c J) x‖ ≤ derivativeConstant c*Real.sqrt ((n+2 : ℕ) : ℝ) := by
    have hg := (field_regularDisorder_ball_bounds (by omega) c J hJ x
      (by simpa only [mem_closedBall, dist_zero_right] using hx)).2.1
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hg
  have hd := (convex_closedBall (0 : Vector (n+2)) (Real.sqrt ((n+2 : ℕ) : ℝ))).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (field_contDiff c J).differentiable (by simp) x) hgrad (hball r hr) (hball q hq)
  have heq := latitudeMap_dist_le (by omega) w hw e he hq hr y hy
  have hmul := mul_le_mul_of_nonneg_left heq
    (mul_nonneg (derivativeConstant_pos c).le (Real.sqrt_nonneg ((n+2 : ℕ) : ℝ)))
  calc
    _ ≤ (derivativeConstant c*Real.sqrt ((n+2 : ℕ) : ℝ))*
      ‖latitudeMap w e q y-latitudeMap w e r y‖ := hd
    _ ≤ _ := by
      apply hmul.trans_eq
      rw [show (derivativeConstant c*Real.sqrt ((n+2 : ℕ) : ℝ))*
        (2*Real.sqrt ((n+2 : ℕ) : ℝ)*Real.sqrt |q-r|)=
          2*derivativeConstant c*(Real.sqrt ((n+2 : ℕ) : ℝ))^2*Real.sqrt |q-r| by ring,
            Real.sq_sqrt (Nat.cast_nonneg _)]

theorem regularDisorder_failure_ennreal {N P : ℕ} (hN : 2 ≤ N) :
    disorderLaw N P (regularDisorder (N := N) (P := P))ᶜ ≤ ENNReal.ofReal (Real.exp (-(N : ℝ))) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (disorderLaw N P) _)]
  exact ENNReal.ofReal_le_ofReal (regularDisorder_failure_probability hN)

end
end SlowEquilibration.SphericalLatitudeChartKacRice
