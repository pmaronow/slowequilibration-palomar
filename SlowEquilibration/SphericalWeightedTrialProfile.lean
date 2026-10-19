-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedTrialUniqueness
public import SlowEquilibration.SphericalBarycenterConstruction

@[expose] public section

/-! # Genuine unique weighted trial profile on all signed latitudes -/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set Filter
open SphericalBarycenter
open scoped Topology
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal signed Dirac upper trial, including the unchanged planted
drift and the source's genuine smooth suppression profile. -/
def weightedAmplitudeTrialProfile (μ : FiniteMixture) (β δ q₁ q₂ r : ℝ) : ℝ :=
  plantedProfileTrial μ β |r|+β^2*(μ.xi r-μ.xi |r|)-
    2*sourceProfile (plantedCoreCost μ β) δ q₁ q₂ r

lemma xi_le_abs (μ : FiniteMixture) (r : ℝ) : μ.xi r≤μ.xi |r| := by
  unfold FiniteMixture.xi
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg p)
  exact (le_abs_self _).trans_eq (abs_pow r p)

lemma plantedProfileTrial_le_annealed_nonnegative (μ : FiniteMixture) {β r : ℝ}
    (hβ : 0≤β) (hβs : β<Thresholds.staticThreshold μ.xi) (hr : r∈Ico (0:ℝ) 1) :
    plantedProfileTrial μ β r≤β^2*μ.xi 1/2 := by
  by_cases hr0 : r=0
  · subst r
    simp [plantedProfileTrial,μ.xi_zero]
  · exact (plantedProfileTrial_lt_annealed μ hβ hβs ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),hr.2⟩).le

/-- The original weighted trial at qStar has exactly its genuine contact value. -/
theorem weightedAmplitudeTrialProfile_qStar (μ : FiniteMixture) {β q₁ q₂ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hc : IsAdmissibleCollar μ β q₁ q₂) (δ : ℝ) :
    weightedAmplitudeTrialProfile μ β δ q₁ q₂ (Thresholds.qStar μ.xi β)=
      β^2*μ.xi 1/2-plantedCoreCost μ β := by
  have hq := (μ.qStar_solves_plateau hβ).1
  unfold weightedAmplitudeTrialProfile sourceProfile
  rw [abs_of_pos hq.1,sub_self,mul_zero,add_zero,
    profile_high _ hc.2.1 hc.2.2.1.le,mul_zero,sub_zero,plantedProfileTrial_qStar_eq]

/-- The source's actual extra suppression gives a full fixed unit gap on
all signed low latitudes; no uniqueness estimate is assumed. -/
theorem weightedAmplitudeTrialProfile_low_gap (μ : FiniteMixture) {β δ q₁ q₂ r : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (hr : r∈Ioo (-1:ℝ) 1) (hrlow : r≤q₁) :
    weightedAmplitudeTrialProfile μ β δ q₁ q₂ r≤
      β^2*μ.xi 1/2-plantedCoreCost μ β-1 := by
  have habs : |r|<1 := abs_lt.mpr hr
  have htrial := plantedProfileTrial_le_annealed_nonnegative μ
    (μ.dynamicalThreshold_pos.trans hβ).le hβs ⟨abs_nonneg r,habs⟩
  have hxi := xi_le_abs μ r
  have hdiff : β^2*(μ.xi r-μ.xi |r|)≤0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β) (sub_nonpos.mpr hxi)
  unfold weightedAmplitudeTrialProfile sourceProfile
  rw [profile_low _ hc.2.1 hrlow]
  unfold sourceK
  nlinarith

/-- Every original signed weighted trial is bounded by the true qStar
contact value, with the collar and source suppression derived internally. -/
theorem weightedAmplitudeTrialProfile_le_contact (μ : FiniteMixture) {β δ q₁ q₂ r : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (hr : r∈Ioo (-1:ℝ) 1) :
    weightedAmplitudeTrialProfile μ β δ q₁ q₂ r≤β^2*μ.xi 1/2-plantedCoreCost μ β := by
  by_cases hrlow : r≤q₁
  · exact (weightedAmplitudeTrialProfile_low_gap μ hβ hβs hc hδ hr hrlow).trans (by linarith)
  · have hrpos : 0<r := hc.1.trans (lt_of_not_ge hrlow)
    have htrial := (plantedProfileTrial_cap_collar_bounds μ hβ hc).1 r ⟨(lt_of_not_ge hrlow).le,hr.2⟩
    have hK : 0 ≤ sourceK (plantedCoreCost μ β) δ := by
      unfold sourceK
      have hJ := plantedCoreCost_pos μ hβ hβs
      linarith
    have hh := profile_nonneg (sourceK (plantedCoreCost μ β) δ) q₁ q₂ hK r
    unfold weightedAmplitudeTrialProfile sourceProfile
    rw [abs_of_pos hrpos,sub_self,mul_zero,add_zero]
    linarith

/-- qStar is the only maximizing original signed weighted latitude. Later
root tangencies and a degenerate maximum are permitted. -/
theorem weightedAmplitudeTrialProfile_unique_maximum (μ : FiniteMixture) {β δ q₁ q₂ r : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (hr : r∈Ioo (-1:ℝ) 1)
    (hmax : β^2*μ.xi 1/2-plantedCoreCost μ β≤weightedAmplitudeTrialProfile μ β δ q₁ q₂ r) :
    r=Thresholds.qStar μ.xi β := by
  by_cases hrlow : r≤q₁
  · have hh := weightedAmplitudeTrialProfile_low_gap μ hβ hβs hc hδ hr hrlow
    linarith
  · have hrpos : 0<r := hc.1.trans (lt_of_not_ge hrlow)
    have hK : 0 ≤ sourceK (plantedCoreCost μ β) δ := by
      unfold sourceK
      have hJ := plantedCoreCost_pos μ hβ hβs
      linarith
    have hh := profile_nonneg (sourceK (plantedCoreCost μ β) δ) q₁ q₂ hK r
    unfold weightedAmplitudeTrialProfile sourceProfile at hmax
    rw [abs_of_pos hrpos,sub_self,mul_zero,add_zero] at hmax
    apply plantedProfileTrial_unique_cap_maximum μ hβ hc ⟨(lt_of_not_ge hrlow).le,hr.2⟩
    rw [plantedProfileTrial_qStar_eq]
    linarith

end
end SlowEquilibration.SphericalModel
