-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSLatitudeTrial
public import SlowEquilibration.CSCalculus

@[expose] public section

/-! Exact Dirac entropy calculus for the genuine latitude first variation.
Both pieces of the inverse-square entropy integral are evaluated by ordinary
interval integration, and then attached to the actual derivative formula. -/

namespace SlowEquilibration.CrisantiSommers
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem dirac_inverseSquare_intervalIntegrable {a b c : ℝ} (ha : a ∈ Ico 0 1)
    (hb : b < 1) (hc : c < 1) :
    IntervalIntegrable (fun t => 1/(xHat (Measure.dirac a) t)^2) volume b c := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div ((xHat_continuous (Measure.dirac a) (dirac_hasCutoff ha)).continuousOn.pow 2)
  intro t ht
  have ht1 : t < 1 := ht.2.trans_lt (max_lt hb hc)
  exact pow_ne_zero 2 (xHat_pos (Measure.dirac a) (dirac_hasCutoff ha) ht1).ne'

theorem integral_dirac_inverseSquare_of_le {a s : ℝ} (_ha : a ∈ Ico 0 1)
    (hs : s ∈ Ico 0 1) (hsa : s ≤ a) :
    (∫ t in (0 : ℝ)..s, 1/(xHat (Measure.dirac a) t)^2) = s/(1-a)^2 := by
  calc
    _ = ∫ _t in (0 : ℝ)..s, 1/(1-a)^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc 0 s := by simpa only [uIcc_of_le hs.1] using ht
      change 1/(xHat (Measure.dirac a) t)^2 = 1/(1-a)^2
      rw [xHat_dirac, max_eq_right (ht'.2.trans hsa)]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one_div]

theorem integral_one_sub_inverseSquare {a s : ℝ} (_ha : a < 1) (hs : s < 1) (has : a ≤ s) :
    (∫ t in a..s, 1/(1-t)^2) = (1-s)⁻¹-(1-a)⁻¹ := by
  have hcont : ContinuousOn (fun t : ℝ => 1/(1-t)^2) (uIcc a s) := by
    apply continuousOn_const.div ((continuous_const.sub continuous_id).continuousOn.pow 2)
    intro t ht
    have ht1 : t < 1 := by
      rw [uIcc_of_le has] at ht
      exact ht.2.trans_lt hs
    exact pow_ne_zero 2 (sub_pos.mpr ht1).ne'
  have hderiv : ∀ t ∈ uIcc a s, HasDerivAt (fun t : ℝ => (1-t)⁻¹) (1/(1-t)^2) t := by
    intro t ht
    have ht1 : t < 1 := by
      rw [uIcc_of_le has] at ht
      exact ht.2.trans_lt hs
    have hh := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).inv (sub_pos.mpr ht1).ne'
    convert hh using 1
    · funext r
      simp only [Pi.inv_apply, Pi.sub_apply, id_eq]
    · simp only [Pi.sub_apply, id_eq, zero_sub, neg_neg]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

theorem integral_dirac_inverseSquare_of_ge {a s : ℝ} (ha : a ∈ Ico 0 1)
    (hs : s ∈ Ico 0 1) (has : a ≤ s) :
    (∫ t in (0 : ℝ)..s, 1/(xHat (Measure.dirac a) t)^2) =
      a/(1-a)^2+(1-s)⁻¹-(1-a)⁻¹ := by
  have htail : (∫ t in a..s, 1/(xHat (Measure.dirac a) t)^2) =
      (1-s)⁻¹-(1-a)⁻¹ := by
    rw [← integral_one_sub_inverseSquare ha.2 hs.2 has]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a s := by simpa only [uIcc_of_le has] using ht
    change 1/(xHat (Measure.dirac a) t)^2 = 1/(1-t)^2
    rw [xHat_dirac, max_eq_left ht'.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (dirac_inverseSquare_intervalIntegrable ha (by norm_num) ha.2)
    (dirac_inverseSquare_intervalIntegrable ha ha.2 hs.2),
    integral_dirac_inverseSquare_of_le ha ha le_rfl, htail]
  ring

theorem firstVariation_dirac_hasDerivAt_of_le (β : ℝ) (η : ℝ → ℝ)
    {a s η' : ℝ} (ha : a ∈ Ico 0 1) (hs : s ∈ Ico 0 1) (hsa : s ≤ a)
    (hη : HasDerivAt η η' s) :
    HasDerivAt (firstVariation β η (Measure.dirac a)) (β^2*η'-s/(1-a)^2) s := by
  have hh := firstVariation_hasDerivAt β η (Measure.dirac a) (dirac_hasCutoff ha) hs.2 hη
  rw [integral_dirac_inverseSquare_of_le ha hs hsa] at hh
  exact hh

theorem firstVariation_dirac_hasDerivAt_of_ge (β : ℝ) (η : ℝ → ℝ)
    {a s η' : ℝ} (ha : a ∈ Ico 0 1) (hs : s ∈ Ico 0 1) (has : a ≤ s)
    (hη : HasDerivAt η η' s) :
    HasDerivAt (firstVariation β η (Measure.dirac a))
      (β^2*η'-(a/(1-a)^2+(1-s)⁻¹-(1-a)⁻¹)) s := by
  have hh := firstVariation_hasDerivAt β η (Measure.dirac a) (dirac_hasCutoff ha) hs.2 hη
  rw [integral_dirac_inverseSquare_of_ge ha hs has] at hh
  exact hh

theorem firstVariation_auxiliary_dirac_deriv_of_le (μ : FiniteMixture) (β : ℝ)
    {q s : ℝ} (hq : q ∈ Ico 0 1) (hs : s ∈ Ico 0 1) (hsa : s ≤ latitudeDiracLocation q) :
    deriv (firstVariation β (μ.auxiliaryCovariance q) (Measure.dirac (latitudeDiracLocation q))) s =
      β^2*(1-q^2)*μ.xi1 (q^2+(1-q^2)*s)-s/(1-latitudeDiracLocation q)^2 := by
  have hh := firstVariation_dirac_hasDerivAt_of_le β (μ.auxiliaryCovariance q)
    (latitudeDiracLocation_mem hq) hs hsa (μ.auxiliaryCovariance_hasDerivAt q s)
  rw [hh.deriv]
  ring

theorem firstVariation_auxiliary_dirac_deriv_of_ge (μ : FiniteMixture) (β : ℝ)
    {q s : ℝ} (hq : q ∈ Ico 0 1) (hs : s ∈ Ico 0 1) (has : latitudeDiracLocation q ≤ s) :
    deriv (firstVariation β (μ.auxiliaryCovariance q) (Measure.dirac (latitudeDiracLocation q))) s =
      β^2*(1-q^2)*μ.xi1 (q^2+(1-q^2)*s)-
        (latitudeDiracLocation q/(1-latitudeDiracLocation q)^2+(1-s)⁻¹-(1-latitudeDiracLocation q)⁻¹) := by
  have hh := firstVariation_dirac_hasDerivAt_of_ge β (μ.auxiliaryCovariance q)
    (latitudeDiracLocation_mem hq) hs has (μ.auxiliaryCovariance_hasDerivAt q s)
  rw [hh.deriv]
  ring

end
end SlowEquilibration.CrisantiSommers
