-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeometricPrefactorBounds
public import SlowEquilibration.SphericalWindowComplexityBounds

/-! Dimension-uniform multiplicative prefactors for the actual mixed and
pure one-point critical-count densities. Both scores here are normalized. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalSequentialRegression WholeFieldRegression
open GOEPhysicalPotential
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

theorem mixedCriticalIntensity_log_prefactor_bound (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g Z : ℝ} (hg : 0 < g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
      z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      |Real.log (mixedCriticalIntensity n μ Q z).toReal - Real.log (n+2 : ℕ) -
        (n+2 : ℕ) * markedComplexity μ Q z| ≤ B := by
  obtain ⟨A,hA,hpref⟩ := sphereKRPrefactor_log_error_bound μ hQ
  obtain ⟨B,hB,hmean⟩ := physicalMean_log_error_bound (Z := Z)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hg
  refine ⟨A + |Real.log (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det)| + B,
    by positivity, ?_⟩
  intro n z hz
  have h1 := hpref n
  have h2 := hmean n (z 1) hz
  have ha := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  rw [mixedCriticalIntensity_log n μ hQ hnp z (by linarith [hz.1]),
    physicalScorePdf_log (n+2) (by omega) μ hQ hnp z]
  unfold markedComplexity
  simp only [Real.log_div hb.ne' ha.ne', Real.log_sqrt hb.le] at h2 ⊢
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [le_abs_self (Real.log (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det)),
    neg_le_abs (Real.log (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det))]

theorem pureCriticalIntensity_log_prefactor_bound
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ h : ℝ,
      (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      |Real.log (pureCriticalIntensity n p hp alpha halpha Q h).toReal -
        Real.log (n+2 : ℕ)/2 -
        (n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h| ≤ B := by
  let μ := FiniteMixture.pure p hp alpha halpha
  obtain ⟨A,hA,hpref⟩ := sphereKRPrefactor_log_error_bound μ hQ
  obtain ⟨B,hB,hmean⟩ := physicalMean_log_error_bound (Z := Z)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hg
  refine ⟨A + |Real.log (2 * Real.pi * μ.xi Q)|/2 + B, by positivity, ?_⟩
  intro n h hh
  have h1 := hpref n
  have h2 := hmean n ((p:ℝ)*h) hh
  have ha := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  rw [pureCriticalIntensity_log n p hp alpha halpha hQ h (by linarith [hh.1]),
    physicalValuePdf_log (n+2) (by omega) μ hQ h]
  unfold pureMarkedComplexity
  dsimp only [μ] at ha hb h1 h2 ⊢
  simp only [Real.log_div hb.ne' ha.ne', Real.log_sqrt hb.le] at h2 ⊢
  rw [show ((n+2:ℕ):ℝ)*h^2 / (2*(FiniteMixture.pure p hp alpha halpha).xi Q) =
    ((n+2:ℕ):ℝ)*(h^2 / (2*(FiniteMixture.pure p hp alpha halpha).xi Q)) by ring]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [le_abs_self (Real.log (2 * Real.pi * μ.xi Q)),
    neg_le_abs (Real.log (2 * Real.pi * μ.xi Q))]

lemma ennreal_mul_exp_bounds_of_log_error {d : ℝ≥0∞} {r T B : ℝ}
    (hr : 0 < r) (hd : 0 < d.toReal) (h : |Real.log d.toReal - Real.log r - T| ≤ B) :
    ENNReal.ofReal (Real.exp (-B) * r * Real.exp T) ≤ d ∧
      d ≤ ENNReal.ofReal (Real.exp B * r * Real.exp T) := by
  have htop : d ≠ ⊤ := by intro he; simp only [he, ENNReal.toReal_top] at hd; exact lt_irrefl _ hd
  have he := ENNReal.ofReal_toReal htop
  have hl : -B + Real.log r + T ≤ Real.log d.toReal := by linarith [(abs_le.mp h).1]
  have hu : Real.log d.toReal ≤ B + Real.log r + T := by linarith [(abs_le.mp h).2]
  have hl' := Real.exp_le_exp.mpr hl
  have hu' := Real.exp_le_exp.mpr hu
  rw [Real.exp_add, Real.exp_add, Real.exp_log hr, Real.exp_log hd] at hl' hu'
  exact ⟨(ENNReal.ofReal_le_ofReal hl').trans_eq he,
    he.symm.trans_le (ENNReal.ofReal_le_ofReal hu')⟩

/-- Genuine bounded multiplicative constants, uniform in every energy and
every radial score in the fixed interval, for all ambient dimensions. -/
theorem actual_mixed_intensity_prefactors (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g Z : ℝ} (hg : 0 < g) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
      z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      ENNReal.ofReal (c * (n+2 : ℕ) * Real.exp ((n+2 : ℕ) * markedComplexity μ Q z)) ≤
        mixedCriticalIntensity n μ Q z ∧
      mixedCriticalIntensity n μ Q z ≤
        ENNReal.ofReal (C * (n+2 : ℕ) * Real.exp ((n+2 : ℕ) * markedComplexity μ Q z)) := by
  obtain ⟨B,hB,hbound⟩ := mixedCriticalIntensity_log_prefactor_bound μ hQ hnp (Z := Z) hg
  refine ⟨Real.exp (-B),Real.exp B,Real.exp_pos _,Real.exp_pos _,?_⟩
  intro n z hz
  exact ennreal_mul_exp_bounds_of_log_error (by positivity)
    (mixedCriticalIntensity_toReal_pos n μ hQ hnp z (by linarith [hz.1])) (hbound n z hz)

/-- Pure normalized energy has the square-root dimension prefactor; its
score support remains exactly the line `(h,p*h)`. -/
theorem actual_pure_intensity_prefactors
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, ∀ h : ℝ,
      (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      ENNReal.ofReal (c * Real.sqrt (n+2 : ℕ) *
        Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h)) ≤
          pureCriticalIntensity n p hp alpha halpha Q h ∧
      pureCriticalIntensity n p hp alpha halpha Q h ≤
        ENNReal.ofReal (C * Real.sqrt (n+2 : ℕ) *
          Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h)) := by
  obtain ⟨B,hB,hbound⟩ := pureCriticalIntensity_log_prefactor_bound p hp alpha halpha hQ (Z := Z) hg
  refine ⟨Real.exp (-B),Real.exp B,Real.exp_pos _,Real.exp_pos _,?_⟩
  intro n h hh
  apply ennreal_mul_exp_bounds_of_log_error (by positivity)
    (pureCriticalIntensity_toReal_pos n p hp alpha halpha hQ h (by linarith [hh.1]))
  rw [Real.log_sqrt (by positivity)]
  exact hbound n h hh

end
end SlowEquilibration.SphericalMarkedWindows
