-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSaddleClearanceChoice
public import SlowEquilibration.SphericalMarkedRawRadialNormalization
public import SlowEquilibration.SphericalMaximumAllDimensionRegularity

@[expose] public section

/-! The mixed radial denominator in the printed §12 Laplace ratio, using the
actual all-critical GOE determinant prefactor. -/

namespace SlowEquilibration.SphericalTAPMixedPhysicalRadialLower
noncomputable section
open Set MeasureTheory Filter
open SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedPhysicalChi SphericalTAPMixedPhysicalRadialBridge
open SphericalTAPMixedSaddleClearanceChoice
open SphericalSequentialRegression GOEPhysicalPotential
open scoped Topology
set_option autoImplicit false

def sourceMixedRadialLaplace (n : ℕ) (μ : FiniteMixture)
    (Q e L R : ℝ) : ℝ :=
  ∫ k in Ioo L R,
    sourceMixedChi n μ Q k * Real.exp ((n+2 : ℕ)*sourceRadialProfile μ Q e k)

theorem sourceAllCriticalRadialWeight_ge_sourceRawRadialWeight
    (n : ℕ) (μ : FiniteMixture) (Q e k : ℝ) :
    sourceRawRadialWeight n μ Q e k ≤ sourceAllCriticalRadialWeight n μ Q e k := by
  unfold sourceRawRadialWeight sourceAllCriticalRadialWeight
  exact mul_le_mul_of_nonneg_left
    (sourceMaximumMean_le_physicalMean n (n+2) (Q^2*μ.xi2 Q) k)
    (Real.exp_pos _).le

theorem sourceAllCriticalRadialWeight_integral_ge_raw
    (n : ℕ) (μ : FiniteMixture) {Q L R : ℝ} (hQ : 0 < Q)
    (hLR : L < R) (e : ℝ) :
    sourceRawRadialNormalization n μ Q (Ioo L R) e ≤
      ∫ k in Ioo L R, sourceAllCriticalRadialWeight n μ Q e k := by
  have hAll := sourceAllCriticalRadialWeight_integrableOn_Ioo n μ hQ e hLR
  have hRawMeas : Measurable (sourceRawRadialWeight n μ Q e) := by
    unfold sourceRawRadialWeight
    have hq : Continuous (fun k : ℝ => scoreQuadratic μ Q (scorePairEquiv (e,k))) :=
      continuous_iff_continuousAt.mpr
        (fun k => (source_scoreQuadratic_radial_hasDerivAt μ Q e k).continuousAt)
    exact (Real.measurable_exp.comp ((measurable_const.mul hq.measurable).div_const _)).mul
      (maximumMean_measurable n (n+2) (Q^2*μ.xi2 Q))
  have hRaw : IntegrableOn (sourceRawRadialWeight n μ Q e) (Ioo L R) := by
    apply hAll.mono' hRawMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
    rw [Real.norm_of_nonneg (sourceRawRadialWeight_nonneg n μ Q e k)]
    exact sourceAllCriticalRadialWeight_ge_sourceRawRadialWeight n μ Q e k
  unfold sourceRawRadialNormalization
  exact setIntegral_mono_on hRaw hAll measurableSet_Ioo
    (fun k _ => sourceAllCriticalRadialWeight_ge_sourceRawRadialWeight n μ Q e k)

theorem sourceAllCriticalRadialWeight_integral_eq_chi
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e L R : ℝ) :
    (∫ k in Ioo L R, sourceAllCriticalRadialWeight n μ Q e k) =
      Real.exp ((n+2 : ℕ)*(Real.log (Q*μ.xi1 Q)/2-1/2)) *
        sourceMixedRadialLaplace n μ Q e L R := by
  unfold sourceMixedRadialLaplace
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (fun k => by
    rw [sourceAllCriticalRadialWeight_eq_chi_profile n μ hQ e k]
    ring))

/-- The all-critical normalized radial integral has the required `N⁻¹ᐟ²`
lower bound on a source-selected energy band, with the A4 clearance now
proved internally for any exterior interval containing the contact mark. -/
theorem sourceMixedRadialLaplace_nearby_lower
    (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L)
    (hm : markK μ β Q ∈ Ioo L R) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
        c*Real.exp ((n+2 : ℕ)*sourceSaddleComplexity μ Q e)/Real.sqrt (n+2 : ℕ) ≤
          sourceMixedRadialLaplace n μ Q e L R := by
  obtain ⟨ε,hε,hclear⟩ := sourceRadialSaddle_nearby_half_clearance μ h hnp hm
  obtain ⟨c,C,hc,hC,hraw⟩ :=
    sourceRawRadialNormalization_band_bounds μ h hnp hL hm hclear
  refine ⟨ε,c,hε,hc,?_⟩
  filter_upwards [hraw] with n hn
  intro e he
  have hAll := sourceAllCriticalRadialWeight_integral_ge_raw n μ
    h.overlap_range.1 (lt_trans hm.1 hm.2) e
  have hraw := (hn e he).1
  have hEq := sourceAllCriticalRadialWeight_integral_eq_chi n μ h.overlap_range.1 e L R
  rw [hEq] at hAll
  let B := Real.log (Q*μ.xi1 Q)/2-1/2
  let T := ((n+2:ℕ):ℝ)*B
  have hT : 0 < Real.exp T := Real.exp_pos _
  have hExp : Real.exp ((n+2:ℕ)*sourceSaddleComplexity μ Q e)*Real.exp T =
      Real.exp ((n+2:ℕ)*(sourceSaddleComplexity μ Q e-1/2+
        Real.log (Q*μ.xi1 Q)/2)) := by
    rw [←Real.exp_add]
    congr 1
    dsimp [T,B]
    ring
  have hbound : Real.exp T *
      (c*Real.exp ((n+2:ℕ)*sourceSaddleComplexity μ Q e)/Real.sqrt (n+2:ℕ)) ≤
      Real.exp T*sourceMixedRadialLaplace n μ Q e L R := by
    calc
      _ = c*(Real.exp ((n+2:ℕ)*sourceSaddleComplexity μ Q e)*Real.exp T)/
          Real.sqrt (n+2:ℕ) := by ring
      _ = c*Real.exp ((n+2:ℕ)*(sourceSaddleComplexity μ Q e-1/2+
          Real.log (Q*μ.xi1 Q)/2))/Real.sqrt (n+2:ℕ) := by rw [hExp]
      _ ≤ sourceRawRadialNormalization n μ Q (Ioo L R) e := hraw
      _ ≤ Real.exp T*sourceMixedRadialLaplace n μ Q e L R := hAll
  exact le_of_mul_le_mul_left hbound hT

end
end SlowEquilibration.SphericalTAPMixedPhysicalRadialLower
