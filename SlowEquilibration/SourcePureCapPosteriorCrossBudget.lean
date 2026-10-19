-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorCrossPolynomial

/-! The full source (9.33) cross-latitude covariance bound, now uniform
for two independently varying latitudes in one cap. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorCrossBudget
noncomputable section
open Set
open SphericalModel SphericalParisiPureLatitudeCovariance
open SphericalTAPCriticalPureLatitudeVariance
open PureStationarity
open SourcePureCapPosteriorCrossKernel
open SourcePureCapPosteriorCrossPolynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem pure_self_residual_eq_variance
    (p : ℕ) (hp : 2 ≤ p) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    let s := Real.sqrt (1-q^2)
    (q^2+s^2)^p-(q^2)^p-
      (p : ℝ)*(q^2)^(p-1)*s^2 =
      sourcePureLatitudeVariance p 1 q := by
  dsimp only
  have hv : 0 ≤ 1-q^2 := by nlinarith [hq.1,hq.2]
  rw [Real.sq_sqrt hv]
  unfold sourcePureLatitudeVariance
  have hnat : (p-1)*2 = p*2-2 := by omega
  ring_nf
  rw [hnat]

/-- The source pure posterior covariance between two latitudes has the
same single subcritical cap budget as the equal-latitude covariance. -/
theorem pure_source_cross_covariance_major_on_cap
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a q₁ q₂ t : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hq₁ : q₁ ∈ Ico a 1) (hq₂ : q₂ ∈ Ico a 1)
    (ht : |t| ≤ 1) :
    let s₁ := Real.sqrt (1-q₁^2)
    let s₂ := Real.sqrt (1-q₂^2)
    |β^2*sourceValueTauCross (FiniteMixture.pure p hp 1 (by positivity))
      1 q₁ q₂ (s₁*s₂*t)| ≤
        pureResidualCoefficient p β a*t^2 := by
  dsimp only
  let s₁ := Real.sqrt (1-q₁^2)
  let s₂ := Real.sqrt (1-q₂^2)
  have hq₁' : q₁ ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans_le hq₁.1,hq₁.2⟩
  have hq₂' : q₂ ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans_le hq₂.1,hq₂.2⟩
  have hpoly := pure_cross_binomial_residual_abs_le_average_self p hp
    hq₁'.1.le hq₂'.1.le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ht
    (q₁ := q₁) (q₂ := q₂) (s₁ := s₁) (s₂ := s₂)
  rw [pure_self_residual_eq_variance p hp hq₁',
    pure_self_residual_eq_variance p hp hq₂'] at hpoly
  have hself₁ : β^2*sourcePureLatitudeVariance p 1 q₁ =
      pureResidualCoefficient p β q₁ := by
    rw [pureResidualCoefficient_eq p hp]
    unfold sourcePureLatitudeVariance
    ring
  have hself₂ : β^2*sourcePureLatitudeVariance p 1 q₂ =
      pureResidualCoefficient p β q₂ := by
    rw [pureResidualCoefficient_eq p hp]
    unfold sourcePureLatitudeVariance
    ring
  have hmono₁ := pureResidualCoefficient_antitoneOn p hp β
    (show a ∈ Icc (0 : ℝ) 1 from ⟨ha.1.le,ha.2.le⟩)
    (show q₁ ∈ Icc (0 : ℝ) 1 from ⟨hq₁'.1.le,hq₁'.2.le⟩) hq₁.1
  have hmono₂ := pureResidualCoefficient_antitoneOn p hp β
    (show a ∈ Icc (0 : ℝ) 1 from ⟨ha.1.le,ha.2.le⟩)
    (show q₂ ∈ Icc (0 : ℝ) 1 from ⟨hq₂'.1.le,hq₂'.2.le⟩) hq₂.1
  have hmean : β^2*((sourcePureLatitudeVariance p 1 q₁+
      sourcePureLatitudeVariance p 1 q₂)/2) ≤
      pureResidualCoefficient p β a := by
    nlinarith [hself₁,hself₂,hmono₁,hmono₂]
  have hraw : |sourceValueTauCross
      (FiniteMixture.pure p hp 1 (by positivity)) 1 q₁ q₂ (s₁*s₂*t)| ≤
      ((sourcePureLatitudeVariance p 1 q₁+
        sourcePureLatitudeVariance p 1 q₂)/2)*t^2 := by
    rw [sourceValueTauCross_pure p hp 1 (by positivity)
      (by norm_num : (0 : ℝ) < 1)]
    simpa only [one_pow,one_mul,mul_assoc] using hpoly
  rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
  calc
    β^2*|sourceValueTauCross
        (FiniteMixture.pure p hp 1 (by positivity)) 1 q₁ q₂ (s₁*s₂*t)| ≤
      β^2*(((sourcePureLatitudeVariance p 1 q₁+
        sourcePureLatitudeVariance p 1 q₂)/2)*t^2) :=
          mul_le_mul_of_nonneg_left hraw (sq_nonneg β)
    _ = (β^2*((sourcePureLatitudeVariance p 1 q₁+
        sourcePureLatitudeVariance p 1 q₂)/2))*t^2 := by ring
    _ ≤ pureResidualCoefficient p β a*t^2 :=
      mul_le_mul_of_nonneg_right hmean (sq_nonneg t)

end
end SlowEquilibration.SourcePureCapPosteriorCrossBudget
