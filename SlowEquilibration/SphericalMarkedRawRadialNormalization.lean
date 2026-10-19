-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedSaddleLaplace
public import SlowEquilibration.NormalizedRadialMeasure

/-! The actual raw determinant-weighted radial normalization and its precise
physical Kac--Rice factor. The raw partition integral and the physical energy
intensity are kept distinct, with their different leading exponents proved. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open GOEMaximumDeterminant GOERawMoments SphericalSequentialRegression
open scoped Topology ENNReal
set_option maxHeartbeats 400000

def sourceRawRadialWeight (n : ℕ) (μ : FiniteMixture) (Q e k : ℝ) : ℝ :=
  Real.exp (-(n+2 : ℕ)*scoreQuadratic μ Q (scorePairEquiv (e,k))/2)*
    maximumMean n (n+2) (Q^2*μ.xi2 Q) k

def sourceRawRadialNormalization (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (U : Set ℝ) (e : ℝ) : ℝ :=
  ∫ k in U,sourceRawRadialWeight n μ Q e k

def sourcePhysicalRadialFactor (n : ℕ) (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  (sphereKRPrefactor (n+1) μ Q).toReal/sourceScoreDenominator μ Q

theorem sourceMaximumMean_nonneg (n N : ℕ) (b k : ℝ) : 0 ≤ maximumMean n N b k := by
  unfold maximumMean matrixAbsoluteDet
  exact integral_nonneg (fun _ => abs_nonneg _)

theorem sourceRawRadialWeight_nonneg (n : ℕ) (μ : FiniteMixture) (Q e k : ℝ) :
    0 ≤ sourceRawRadialWeight n μ Q e k :=
  mul_nonneg (Real.exp_pos _).le (sourceMaximumMean_nonneg _ _ _ _)

theorem sourcePhysicalRadialFactor_pos (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) : 0 < sourcePhysicalRadialFactor n μ Q :=
  div_pos (ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ)
    (sphereKRPrefactor_ne_top (n+1) μ Q)) (sourceScoreDenominator_pos μ hQ hnp)

/-- Exact physical energy density, with its actual raw determinant weight. -/
theorem sourceEnergyRadialDensity_eq_raw (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (e k : ℝ) :
    sourceEnergyRadialDensity n μ Q e k=
      sourcePhysicalRadialFactor n μ Q*sourceRawRadialWeight n μ Q e k := by
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hD := sourceScoreDenominator_pos μ hQ hnp
  unfold sourceEnergyRadialDensity mixedLocalMaxPhysicalIntensity mixedNegativeIntensity physicalScorePdf
  simp only [mul_div_cancel_left₀ _ hN.ne',ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hN.le)]
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  change ((n+2 : ℕ) : ℝ)⁻¹*((sphereKRPrefactor (n+1) μ Q).toReal*
    (ENNReal.ofReal (((n+2 : ℕ) : ℝ)/sourceScoreDenominator μ Q*
      Real.exp (-(n+2 : ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (e,k))))).toReal*
    (ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) k)).toReal)=_
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ ((n+2 : ℕ) : ℝ)/sourceScoreDenominator μ Q*
    Real.exp (-(n+2 : ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (e,k))))]
  rw [ENNReal.toReal_ofReal (sourceMaximumMean_nonneg _ _ _ _)]
  unfold sourcePhysicalRadialFactor sourceRawRadialWeight
  rw [show -(n+2 : ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (e,k))=
    -(n+2 : ℕ)*scoreQuadratic μ Q (scorePairEquiv (e,k))/2 by ring]
  field_simp

theorem sourceMaximumEnergyDensity_eq_raw (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (U : Set ℝ) (e : ℝ) :
    sourceMaximumEnergyDensity n μ Q U ((n+2 : ℕ)*e)=
      sourcePhysicalRadialFactor n μ Q*sourceRawRadialNormalization n μ Q U e := by
  unfold sourceMaximumEnergyDensity sourceRawRadialNormalization
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (sourceEnergyRadialDensity_eq_raw n μ hQ hnp e)

theorem sourcePhysicalRadialFactor_exponential_bounds (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      c*Real.exp ((n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2)) ≤ sourcePhysicalRadialFactor n μ Q ∧
      sourcePhysicalRadialFactor n μ Q ≤ C*Real.exp ((n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2)) := by
  obtain ⟨B,_hB,hError⟩ := sphereKRPrefactor_log_error_bound μ hQ
  have hD := sourceScoreDenominator_pos μ hQ hnp
  refine ⟨Real.exp (-B)/sourceScoreDenominator μ Q,Real.exp B/sourceScoreDenominator μ Q,
    div_pos (Real.exp_pos _) hD,div_pos (Real.exp_pos _) hD,?_⟩
  intro n
  have hP := ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ) (sphereKRPrefactor_ne_top (n+1) μ Q)
  have hLower : -B+(n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2) ≤
      Real.log (sphereKRPrefactor (n+1) μ Q).toReal := by linarith [(abs_le.mp (hError n)).1]
  have hUpper : Real.log (sphereKRPrefactor (n+1) μ Q).toReal ≤
      B+(n+2 : ℕ)*((1-Real.log (Q*μ.xi1 Q))/2) := by linarith [(abs_le.mp (hError n)).2]
  have hl := Real.exp_le_exp.mpr hLower
  have hu := Real.exp_le_exp.mpr hUpper
  rw [Real.exp_log hP,Real.exp_add] at hl hu
  unfold sourcePhysicalRadialFactor
  constructor
  · convert div_le_div_of_nonneg_right hl hD.le using 1
    ring
  · convert div_le_div_of_nonneg_right hu hD.le using 1
    ring

/-- Source10.5(c), for the original raw normalization rather than the
physical energy density, with the exact additional exponential factor. -/
theorem sourceRawRadialNormalization_band_bounds (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hA4 : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      sourceRadialClearance μ β Q (Ioo L R)/2 ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      c*Real.exp ((n+2 : ℕ)*(sourceSaddleComplexity μ Q e-1/2+Real.log (Q*μ.xi1 Q)/2))/Real.sqrt (n+2 : ℕ) ≤
        sourceRawRadialNormalization n μ Q (Ioo L R) e ∧
      sourceRawRadialNormalization n μ Q (Ioo L R) e ≤
        C*Real.exp ((n+2 : ℕ)*(sourceSaddleComplexity μ Q e-1/2+Real.log (Q*μ.xi1 Q)/2))/Real.sqrt (n+2 : ℕ) := by
  obtain ⟨c,C,hc,hC,hBand⟩ := sourceSaddle_radial_normalization μ h hnp hL hm hA4
  obtain ⟨p,P,hp,hP,hPref⟩ := sourcePhysicalRadialFactor_exponential_bounds μ h.overlap_range.1 hnp
  refine ⟨c/P,C/p,div_pos hc hP,div_pos hC hp,?_⟩
  filter_upwards [hBand] with n hn
  intro e he
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hS := Real.sqrt_pos.mpr hN
  have hDensity := hn e he
  rw [sourceMaximumEnergyDensity_eq_raw n μ h.overlap_range.1 hnp] at hDensity
  have hZ : 0 ≤ sourceRawRadialNormalization n μ Q (Ioo L R) e :=
    integral_nonneg (fun k => sourceRawRadialWeight_nonneg n μ Q e k)
  have hmulL := mul_le_mul_of_nonneg_right (hPref n).2 hZ
  have hmulU := mul_le_mul_of_nonneg_right (hPref n).1 hZ
  let γ := (1-Real.log (Q*μ.xi1 Q))/2
  have hExp : Real.exp ((n+2 : ℕ)*(sourceSaddleComplexity μ Q e-1/2+Real.log (Q*μ.xi1 Q)/2))=
      Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)/Real.exp ((n+2 : ℕ)*γ) := by
    rw [←Real.exp_sub]
    congr 1
    dsimp [γ]
    ring
  rw [hExp]
  constructor
  · have hProd : c*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)/Real.sqrt (n+2 : ℕ) ≤
        sourceRawRadialNormalization n μ Q (Ioo L R) e*(P*Real.exp ((n+2 : ℕ)*γ)) :=
      (hDensity.1.trans hmulL).trans_eq (mul_comm _ _)
    have hh := (div_le_iff₀ (mul_pos hP (Real.exp_pos ((n+2 : ℕ)*γ)))).mpr hProd
    convert hh using 1
    field_simp
  · have hProd : sourceRawRadialNormalization n μ Q (Ioo L R) e*(p*Real.exp ((n+2 : ℕ)*γ)) ≤
        C*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)/Real.sqrt (n+2 : ℕ) :=
      (mul_comm _ _).trans_le (hmulU.trans hDensity.2)
    have hh := (le_div_iff₀ (mul_pos hp (Real.exp_pos ((n+2 : ℕ)*γ)))).mpr hProd
    convert hh using 1
    field_simp
end SlowEquilibration.SphericalMarkedWindows
