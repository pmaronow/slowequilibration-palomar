-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GOEMaximumAllDimensionPositivity
public import SlowEquilibration.SphericalMarkedRawRadialNormalization
public import SlowEquilibration.SphericalMaximumEnergyRegularity

/-! Actual positivity and radial integrability in every dimension and every
physical energy, including the finite prefix omitted by asymptotic estimates. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open GOEMaximumDeterminant GOERawMoments GOEPhysicalPotential SphericalSequentialRegression
open GaussianRadialEnergyTilt RadialGaussianBounds
open UnrestrictedConditionedDeterminants
open scoped Topology ENNReal
set_option maxHeartbeats 400000

theorem sourceMaximumMean_le_physicalMean (n N : ℕ) (b k : ℝ) :
    maximumMean n N b k ≤ physicalMean n N b k := by
  have hi : Integrable (matrixAbsoluteDet n k) (SphericalGaussianJet.goeLaw (n+1) N b) := by
    have he (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : |(W-k • 1).det|=matrixAbsoluteDet n k W := by
      unfold matrixAbsoluteDet
      rw [show W-k • 1=-(k • 1-W) by module,Matrix.det_neg,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    simpa only [he] using (fixed_shifted_determinant_integrable (n+1) N b k).abs
  exact setIntegral_le_integral hi (ae_of_all _ (fun _ => abs_nonneg _))

theorem mixedLocalMaxPhysicalIntensity_le_critical_all_dimensions (n : ℕ) (μ : FiniteMixture)
    (Q H k : ℝ) : mixedLocalMaxPhysicalIntensity n μ Q H k ≤ mixedCriticalPhysicalIntensity n μ Q H k := by
  unfold mixedLocalMaxPhysicalIntensity mixedCriticalPhysicalIntensity mixedNegativeIntensity mixedCriticalIntensity
  exact mul_le_mul_right (mul_le_mul_right (ENNReal.ofReal_le_ofReal
    (sourceMaximumMean_le_physicalMean n (n+2) (Q^2*μ.xi2 Q) k)) _) _

theorem sourceBaselineDensity_integrable_all_dimensions (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) :
    IntegrableOn (sourceBaselineDensity n μ β x Q) (Ioo L R) := by
  let d := (L-sourceRadialEdge μ Q)/2
  have hd : 0 < d := by dsimp [d];linarith
  obtain ⟨c,C,_hc,hC,hBounds⟩ := actual_mixed_intensity_prefactors μ h.overlap_range.1 hnp (Z := R) hd
  have hProfile := sourceBaseline_profile_bounds μ h hnp hL hm
  let a := sourceRadialCurvature μ Q/2
  have ha := half_pos (sourceRadialCurvature_pos μ h.overlap_range.1 hnp)
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  apply (((gaussian_integrable (mul_pos ha hN) (markK μ β Q)).const_mul C).restrict).mono'
  · exact (sourceBaselineDensity_measurable n μ β x Q).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
    have hkR : k ∈ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+d) R := by
      constructor
      · dsimp [d,sourceRadialEdge] at *
        linarith [hk.1]
      · exact hk.2.le
    have hBound := mul_le_mul_right (hBounds n (scorePairEquiv (markE μ β x Q,k)) hkR).2
      (ENNReal.ofReal ((n+2 : ℕ) : ℝ)⁻¹)
    rw [inverse_dimension_prefactor] at hBound
    have he : mixedCriticalPhysicalIntensity n μ Q ((n+2 : ℕ)*markE μ β x Q) k ≤
        ENNReal.ofReal (C*Real.exp ((n+2 : ℕ)*sourceRadialProfile μ Q (markE μ β x Q) k)) := by
      simpa only [mixedCriticalPhysicalIntensity,mul_div_cancel_left₀ _ hN.ne',scorePairEquiv_apply,sourceRadialProfile] using hBound
    have hMax := (mixedLocalMaxPhysicalIntensity_le_critical_all_dimensions n μ Q
      ((n+2 : ℕ)*markE μ β x Q) k).trans he
    have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMax
    rw [ENNReal.toReal_ofReal (by positivity)] at hu
    rw [Real.norm_of_nonneg (show 0 ≤ sourceBaselineDensity n μ β x Q k from ENNReal.toReal_nonneg)]
    apply hu.trans
    unfold gaussian
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    have hp := (hProfile k hk).2
    nlinarith

theorem sourceMaximumRadialDensity_integrable_all_dimensions (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (H : ℝ) :
    IntegrableOn (fun k => (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal) (Ioo L R) := by
  let m := markK μ β Q
  let M := max (m-L) (R-m)
  have hRadius : ∀ k ∈ Ioo L R,|k-m| ≤ M := by
    intro k hk
    have hl := le_max_left (m-L) (R-m)
    have hr := le_max_right (m-L) (R-m)
    exact abs_le.mpr (by constructor <;> linarith [hk.1,hk.2])
  have hi := tiltedDensity_integrableOn (B := sourceEnergyRadialCross μ Q) (c₀ := β*x) measurableSet_Ioo
    (sourceBaselineDensity_integrable_all_dimensions n μ h hnp hL hm)
    (fun _ _ => ENNReal.toReal_nonneg) (sourceEnergyCurvature_pos μ h.overlap_range.1 hnp).le
    (by positivity : 0 < ((n+2 : ℕ) : ℝ)) hRadius (H-(n+2 : ℕ)*markE μ β x Q)
  apply hi.congr
  exact ae_of_all _ (fun k => by
    have he := physicalMaximumDensity_eq_tilt n μ h hnp (H-(n+2 : ℕ)*markE μ β x Q) k
    rw [show (n+2 : ℕ)*markE μ β x Q+(H-(n+2 : ℕ)*markE μ β x Q)=H by ring] at he
    exact he.symm)

theorem sourceEnergyRadialDensity_pos_all_dimensions (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (e : ℝ) {k : ℝ} (hk : 0 < k) :
    0 < sourceEnergyRadialDensity n μ Q e k := by
  rw [sourceEnergyRadialDensity_eq_raw n μ hQ hnp]
  exact mul_pos (sourcePhysicalRadialFactor_pos n μ hQ hnp)
    (mul_pos (Real.exp_pos _) (maximumMean_pos_all_dimensions n (by omega)
      (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hk))

/-- Actual source radial intensity is positive at every physical energy in
EVERY dimension, using genuine determinant-weighted Gaussian positivity. -/
theorem sourceMaximumEnergyDensity_pos_all_dimensions (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (H : ℝ) :
    0 < sourceMaximumEnergyDensity n μ Q (Ioo L R) H := by
  have hi := sourceMaximumRadialDensity_integrable_all_dimensions n μ h hnp hL hm H
  have hPos (k : ℝ) (hk : k ∈ Ioo L R) : 0 < (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal := by
    have he := sourceEnergyRadialDensity_pos_all_dimensions n μ h.overlap_range.1 hnp
      (H/(n+2 : ℕ)) (k := k) (by
        have hEdge : 0 ≤ sourceRadialEdge μ Q := by unfold sourceRadialEdge;positivity
        linarith [hk.1])
    simpa only [sourceEnergyRadialDensity,mul_div_cancel₀ _ (by positivity : ((n+2 : ℕ) : ℝ) ≠ 0)] using he
  apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun _ => ENNReal.toReal_nonneg)) hi).mpr
  have hSub : Ioo L R ⊆ Function.support (fun k => (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal) ∩ Ioo L R :=
    fun k hk => ⟨(hPos k hk).ne',hk⟩
  exact (isOpen_Ioo.measure_pos volume ⟨markK μ β Q,hm⟩).trans_le (measure_mono hSub)
end SlowEquilibration.SphericalMarkedWindows
