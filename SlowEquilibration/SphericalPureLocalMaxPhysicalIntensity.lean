-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLocalMaxPhysicalIntensity

/-! Proper pure local-maximum intensities in the actual unnormalized energy
coordinate, with the exact inverse-square-root dimension prefactor. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalSequentialRegression
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pureLocalMaxPhysicalIntensity (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) (Q H : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹ * pureNegativeIntensity n p hp alpha halpha Q (H/(n+2 : ℕ))

def pureCriticalPhysicalIntensity (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) (Q H : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹ * pureCriticalIntensity n p hp alpha halpha Q (H/(n+2 : ℕ))

theorem actual_pure_localMax_physical_intensity (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (I : Set ℝ) (hI : MeasurableSet I) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualLocalMaxCount (n+1) c (physicalEnergyWindow (n+2) I univ) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ H in I, pureLocalMaxPhysicalIntensity n p hp alpha halpha Q H := by
  dsimp only
  have hw : MeasurableSet (physicalEnergyWindow (n+2) I univ) :=
    rectangularScoreWindow_measurable _ _ (hI.preimage (measurable_const_mul ((n+2 : ℕ):ℝ))) MeasurableSet.univ
  rw [(actual_pure_localMax_count_intensity n p hp alpha halpha hQ _ hw).2]
  have he : pureScoreWindow p (physicalEnergyWindow (n+2) I univ) =
      (fun h : ℝ => ((n+2 : ℕ):ℝ)*h) ⁻¹' I := by
    ext h
    simp [pureScoreWindow,physicalEnergyWindow,rectangularScoreWindow,pureScoreLine]
  rw [he]
  exact setLIntegral_positive_rescale (n+2 : ℕ) (by positivity) I _

lemma inverse_sqrt_dimension_prefactor (n : ℕ) (c T : ℝ) :
    ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹ * ENNReal.ofReal (c*Real.sqrt (n+2 : ℕ)*Real.exp T) =
      ENNReal.ofReal (c*(Real.sqrt (n+2 : ℕ))⁻¹*Real.exp T) := by
  have hN : (0:ℝ)<(n+2 : ℕ) := by positivity
  have hs : Real.sqrt (n+2 : ℕ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have he : (((n+2 : ℕ):ℝ)⁻¹ * Real.sqrt (n+2 : ℕ)) = (Real.sqrt (n+2 : ℕ))⁻¹ := by
    rw [← one_div (Real.sqrt (n+2 : ℕ))]
    apply (eq_div_iff hs).mpr
    rw [mul_assoc,← pow_two,Real.sq_sqrt hN.le,inv_mul_cancel₀ hN.ne']
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    _ = c*(((n+2 : ℕ):ℝ)⁻¹ * Real.sqrt (n+2 : ℕ))*Real.exp T := by ring
    _ = _ := by rw [he]

theorem pure_localMax_physical_prefactors (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ e : ℝ,
      (p:ℝ)*e ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z →
      ENNReal.ofReal (c*(Real.sqrt (n+2 : ℕ))⁻¹ *
        Real.exp ((n+2 : ℕ)*pureMarkedComplexity p hp alpha halpha Q e)) ≤
        pureLocalMaxPhysicalIntensity n p hp alpha halpha Q ((n+2 : ℕ)*e) ∧
      pureLocalMaxPhysicalIntensity n p hp alpha halpha Q ((n+2 : ℕ)*e) ≤
        pureCriticalPhysicalIntensity n p hp alpha halpha Q ((n+2 : ℕ)*e) ∧
      pureCriticalPhysicalIntensity n p hp alpha halpha Q ((n+2 : ℕ)*e) ≤
        ENNReal.ofReal (C*(Real.sqrt (n+2 : ℕ))⁻¹ *
          Real.exp ((n+2 : ℕ)*pureMarkedComplexity p hp alpha halpha Q e)) := by
  obtain ⟨c,C,hc,hC,hm⟩ := actual_pure_negative_intensity_prefactors p hp alpha halpha hQ (Z := Z) hg
  obtain ⟨a,B,ha,hB,hall⟩ := actual_pure_intensity_prefactors p hp alpha halpha hQ (Z := Z) hg
  refine ⟨c,B,hc,hB,?_⟩
  filter_upwards [hm,pureNegativeIntensity_comparison p hp alpha halpha hQ (Z := Z) hg] with n hn hcomp
  intro e he
  have heq : (((n+2 : ℕ):ℝ)*e)/(n+2 : ℕ)=e := mul_div_cancel_left₀ _ (by positivity)
  simp only [pureLocalMaxPhysicalIntensity,pureCriticalPhysicalIntensity,heq]
  have h1 := mul_le_mul_right (hn e he).1 (ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹)
  have h2 := mul_le_mul_right (hcomp e he).2 (ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹)
  have h3 := mul_le_mul_right (hall n e he).2 (ENNReal.ofReal ((n+2 : ℕ):ℝ)⁻¹)
  rw [inverse_sqrt_dimension_prefactor] at h1 h3
  exact ⟨h1,h2,h3⟩

end
end SlowEquilibration.SphericalMarkedWindows
