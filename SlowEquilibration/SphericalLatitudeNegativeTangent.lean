-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCovariance
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

/-! # The actual odd-mixture latitude tangent error

For every positive compact latitude window the true covariance supporting
line is valid above a fixed negative transverse cutoff. Its only possible
deficit is bounded by a fixed constant times the actual negative-overlap
indicator. This includes odd mixtures with a quadratic component.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal covariance tangent deficit in the latitude Guerra kernel. -/
def latitudeTangentDeficit (μ : FiniteMixture) (q t : ℝ) : ℝ :=
  μ.xi q+μ.xi1 q*(q^2+(1-q^2)*t-q)-μ.xi (q^2+(1-q^2)*t)

theorem latitudeTangentDeficit_continuous (μ : FiniteMixture) :
    Continuous (fun z : ℝ × ℝ => latitudeTangentDeficit μ z.1 z.2) := by
  have hxi : Continuous μ.xi := continuous_iff_continuousAt.mpr (fun r => (μ.hasDerivAt_xi r).continuousAt)
  have hxi1 : Continuous μ.xi1 := continuous_iff_continuousAt.mpr (fun r => (μ.hasDerivAt_xi1 r).continuousAt)
  unfold latitudeTangentDeficit
  exact ((hxi.comp continuous_fst).add ((hxi1.comp continuous_fst).mul
    (((continuous_fst.pow 2).add ((continuous_const.sub (continuous_fst.pow 2)).mul continuous_snd)).sub continuous_fst))).sub
      (hxi.comp ((continuous_fst.pow 2).add ((continuous_const.sub (continuous_fst.pow 2)).mul continuous_snd)))

/-- All finite mixtures obey their true tangent inequality uniformly above
the predetermined cutoff -δ²/2 in a positive latitude window. -/
theorem latitude_tangent_le_of_transverse_lower (μ : FiniteMixture) {δ ρ q t : ℝ}
    (hδ : 0 < δ) (hρ : ρ < 1) (hq : q ∈ Icc δ ρ)
    (ht : -(δ^2/2) ≤ t) :
    μ.xi q+μ.xi1 q*(q^2+(1-q^2)*t-q) ≤ μ.xi (q^2+(1-q^2)*t) := by
  have hq0 : 0 ≤ q := hδ.le.trans hq.1
  have hq1 : q ≤ 1 := hq.2.trans hρ.le
  have hA0 : 0 ≤ 1-q^2 := by nlinarith
  have hA1 : 1-q^2 ≤ 1 := by nlinarith [sq_nonneg q]
  have hδ2 : 0 ≤ δ^2/2 := by positivity
  have hprod := mul_le_mul_of_nonneg_left ht hA0
  have hprod2 := mul_le_mul_of_nonneg_right hA1 hδ2
  have hqδ : δ^2 ≤ q^2 := by nlinarith [hq.1]
  have harg : 0 ≤ q^2+(1-q^2)*t := by nlinarith
  exact μ.xi_tangent_le_of_nonneg hq0 harg

/-- A genuine fixed negative cutoff and covariance-error constant for the
actual odd-mixture comparison. The only nonzero error is attached to the
literal event t < -η; neither positivity nor a pressure estimate is assumed. -/
theorem exists_uniform_latitude_tangent_deficit_bound (μ : FiniteMixture) {δ ρ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ < 1) :
    ∃ η C : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ q ∈ Icc δ ρ, ∀ t ∈ Icc (-1 : ℝ) 1,
        latitudeTangentDeficit μ q t ≤ C*({s : ℝ | s < -η}.indicator (fun _ => (1 : ℝ))) t := by
  let η := δ^2/2
  have hη : 0 < η := by dsimp only [η]; positivity
  have hδ1 : δ < 1 := hδρ.trans_lt hρ
  have hη1 : η ≤ 1 := by dsimp only [η]; nlinarith
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a := δ) (b := ρ)).prod
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    (latitudeTangentDeficit_continuous μ).continuousOn
  let C' := max C 0
  refine ⟨η,C',hη,hη1,le_max_right _ _,?_⟩
  intro q hq t ht
  by_cases hneg : t < -η
  · rw [indicator_of_mem (show t∈{s : ℝ | s < -η} from hneg),mul_one]
    have hb : |latitudeTangentDeficit μ q t| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (q,t) ⟨hq,ht⟩
    exact (le_abs_self _).trans (hb.trans (le_max_left _ _))
  · rw [indicator_of_notMem (show t∉{s : ℝ | s < -η} from hneg),mul_zero]
    have hv := latitude_tangent_le_of_transverse_lower μ hδ hρ hq (le_of_not_gt hneg)
    unfold latitudeTangentDeficit
    linarith

end
end SlowEquilibration.SphericalModel
