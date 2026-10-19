-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureOnePointActualMeanTangent
public import SlowEquilibration.SphericalCountIntensityRates
public import SlowEquilibration.SphericalPureLocalMaxPhysicalIntensity

/-! Exact relation between the actual proper-pure Kac--Rice physical energy
density and its absolute-GOE energy log-weight. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter GOEPhysicalPotential GOEPhysicalNormalizedMoments
open SphericalSequentialRegression TwoAtomStationarity SphericalTAPCertificate
open scoped Topology ENNReal
set_option maxHeartbeats 500000

theorem pureCriticalPhysicalIntensity_toReal_pos
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (H : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q) <
      (p : ℝ)*H/(n+2 : ℕ)) :
    0 < (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal := by
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hEdge' : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q) <
      (p : ℝ)*(H/(n+2 : ℕ)) := by convert hEdge using 1; ring
  have hCrit := pureCriticalIntensity_toReal_pos n p hp a ha hQ _ hEdge'
  unfold pureCriticalPhysicalIntensity
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hN.le)]
  exact mul_pos (inv_pos.mpr hN) hCrit

/-- The geometric sphere factor and scalar Gaussian normalization are
energy-independent. The sole energy dependence is the actual Gaussian plus
ordinary absolute determinant log-weight. -/
theorem pureCriticalPhysicalIntensity_log_eq_weight
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (H : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q) <
      (p : ℝ)*H/(n+2 : ℕ)) :
    let μ := FiniteMixture.pure p hp a ha
    let V := μ.xi Q
    let b := Q^2*μ.xi2 Q
    Real.log (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal =
      Real.log (((n+2 : ℕ) : ℝ)⁻¹)+
        Real.log (sphereKRPrefactor (n+1) μ Q).toReal+
        (Real.log (n+2 : ℕ)-Real.log (2*Real.pi*V))/2+
          pureActualEnergyLogWeight n V b (p : ℝ) H := by
  let μ := FiniteMixture.pure p hp a ha
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hEdge' : 2*Real.sqrt b < (p : ℝ)*(H/(n+2 : ℕ)) := by
    convert hEdge using 1; ring
  have hCritPos : 0 < (pureCriticalIntensity n p hp a ha Q (H/(n+2 : ℕ))).toReal :=
    pureCriticalIntensity_toReal_pos n p hp a ha hQ _ hEdge'
  have hCritLog := pureCriticalIntensity_log n p hp a ha hQ (H/(n+2 : ℕ)) hEdge'
  change Real.log (pureCriticalIntensity n p hp a ha Q (H/(n+2 : ℕ))).toReal =
    Real.log (sphereKRPrefactor (n+1) μ Q).toReal+
      Real.log (physicalValuePdf (n+2) μ Q (H/(n+2 : ℕ))).toReal+
      Real.log (physicalMean n (n+2) b ((p : ℝ)*(H/(n+2 : ℕ)))) at hCritLog
  have hPdf := physicalValuePdf_log (n+2) (by omega) μ hQ (H/(n+2 : ℕ))
  change Real.log (physicalValuePdf (n+2) μ Q (H/(n+2 : ℕ))).toReal =
    (Real.log (n+2 : ℕ)-Real.log (2*Real.pi*V))/2-
      (n+2 : ℕ)*(H/(n+2 : ℕ))^2/(2*V) at hPdf
  have hIntensity :
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal =
        Real.log (((n+2 : ℕ) : ℝ)⁻¹)+
          Real.log (pureCriticalIntensity n p hp a ha Q (H/(n+2 : ℕ))).toReal := by
    unfold pureCriticalPhysicalIntensity
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hN.le),
      Real.log_mul (inv_pos.mpr hN).ne' hCritPos.ne']
  rw [hIntensity,hCritLog,hPdf]
  unfold pureActualEnergyLogWeight
  have harg : (p : ℝ)*(H/(n+2 : ℕ))=(p : ℝ)*H/(n+2 : ℕ) := by ring
  rw [harg]
  have hGaussian : (n+2 : ℕ)*(H/(n+2 : ℕ))^2/(2*V)=
      H^2/(2*(n+2 : ℕ)*V) := by field_simp
  rw [hGaussian]
  ring

/-- Exact cancellation of every geometric and scalar-density prefactor
between two exterior physical-energy arguments in the actual count density. -/
theorem pureCriticalPhysicalIntensity_log_shift_eq_weight
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (H₁ H₂ : ℝ)
    (hEdge₁ : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q) <
      (p : ℝ)*H₁/(n+2 : ℕ))
    (hEdge₂ : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q) <
      (p : ℝ)*H₂/(n+2 : ℕ)) :
    let μ := FiniteMixture.pure p hp a ha
    let V := μ.xi Q
    let b := Q^2*μ.xi2 Q
    Real.log (pureCriticalPhysicalIntensity n p hp a ha Q H₂).toReal-
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q H₁).toReal =
        pureActualEnergyLogWeight n V b (p : ℝ) H₂-
          pureActualEnergyLogWeight n V b (p : ℝ) H₁ := by
  rw [pureCriticalPhysicalIntensity_log_eq_weight n p hp a ha hQ H₂ hEdge₂,
    pureCriticalPhysicalIntensity_log_eq_weight n p hp a ha hQ H₁ hEdge₁]
  ring

/-- At every logarithmically centered proper-pure source energy, the actual
all-critical physical Kac--Rice intensity has the manuscript's fixed-shift
logarithmic ratio. -/
theorem sourcePure_criticalPhysicalIntensity_log_fixed_shift
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ))
    (t : ℝ) :
    Tendsto (fun n : ℕ =>
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q+σ n+t)).toReal-
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q+σ n)).toReal)
      atTop (𝓝 (-(β*x)*t)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let b := Q^2*μ.xi2 Q
  let k₁ : ℕ → ℝ := fun n => (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ)
  let k₂ : ℕ → ℝ := fun n => (p : ℝ)*((n+2 : ℕ)*E+σ n+t)/(n+2 : ℕ)
  have hContact : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hk₁ : Tendsto k₁ atTop (𝓝 ((p : ℝ)*E)) := by
    have hh := ((tendsto_const_nhds (x := E)).add hσzero).const_mul (p : ℝ)
    convert hh using 1
    · funext n
      dsimp [k₁]
      field_simp
    · ring
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have htzero : Tendsto (fun n : ℕ => (p : ℝ)*t/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
    hN.const_div_atTop ((p : ℝ)*t)
  have hk₂ : Tendsto k₂ atTop (𝓝 ((p : ℝ)*E)) := by
    have hh := hk₁.add htzero
    convert hh using 1
    · funext n
      dsimp [k₁,k₂]
      field_simp
    · ring
  have hEdge₁ : ∀ᶠ n : ℕ in atTop, 2*Real.sqrt b < k₁ n :=
    hk₁.eventually (Ioi_mem_nhds hContact)
  have hEdge₂ : ∀ᶠ n : ℕ in atTop, 2*Real.sqrt b < k₂ n :=
    hk₂.eventually (Ioi_mem_nhds hContact)
  have hEq : (fun n : ℕ =>
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n+t)).toReal-
      Real.log (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal)
      =ᶠ[atTop] (fun n : ℕ =>
        pureActualEnergyLogWeight n (μ.xi Q) b (p : ℝ) ((n+2 : ℕ)*E+σ n+t)-
          pureActualEnergyLogWeight n (μ.xi Q) b (p : ℝ) ((n+2 : ℕ)*E+σ n)) := by
    filter_upwards [hEdge₁,hEdge₂] with n hn₁ hn₂
    exact pureCriticalPhysicalIntensity_log_shift_eq_weight n p hp a ha
      h.overlap_range.1 _ _ hn₁ hn₂
  have hWeight := sourcePure_actualEnergyLogWeight_fixed_shift p hp a ha h hD σ hσ t
  exact hWeight.congr' hEq.symm

/-- Consequently the ratio of the two genuine physical Kac--Rice energy
densities converges to the source exponential, for any fixed displacement
around any logarithmically centered energy. -/
theorem sourcePure_criticalPhysicalIntensity_fixed_shift_ratio
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ))
    (t : ℝ) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    Tendsto (fun n : ℕ =>
      (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n+t)).toReal/
        (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal)
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let b := Q^2*μ.xi2 Q
  have hContact : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have htzero : Tendsto (fun n : ℕ => t/(n+2 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
    hN.const_div_atTop t
  have hShift : Tendsto (fun n : ℕ => E+σ n/(n+2 : ℕ)) atTop (𝓝 E) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := E)).add hσzero
  have hShiftT : Tendsto (fun n : ℕ => E+σ n/(n+2 : ℕ)+t/(n+2 : ℕ))
      atTop (𝓝 E) := by
    simpa only [add_zero] using hShift.add htzero
  have hK₁ := hShift.const_mul (p : ℝ)
  have hK₂ := hShiftT.const_mul (p : ℝ)
  have hEdge₁ : ∀ᶠ n : ℕ in atTop,
      2*Real.sqrt b < (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ) := by
    filter_upwards [hK₁.eventually (Ioi_mem_nhds hContact)] with n hn
    convert hn using 1; field_simp
  have hEdge₂ : ∀ᶠ n : ℕ in atTop,
      2*Real.sqrt b < (p : ℝ)*((n+2 : ℕ)*E+σ n+t)/(n+2 : ℕ) := by
    filter_upwards [hK₂.eventually (Ioi_mem_nhds hContact)] with n hn
    convert hn using 1; field_simp
  have hLog := sourcePure_criticalPhysicalIntensity_log_fixed_shift p hp a ha h hD σ hσ t
  have hExp := hLog.exp
  rw [←Real.exp_eq_exp_ℝ] at hExp
  have hEq : (fun n : ℕ =>
      Real.exp (Real.log (pureCriticalPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E+σ n+t)).toReal-
        Real.log (pureCriticalPhysicalIntensity n p hp a ha Q
          ((n+2 : ℕ)*E+σ n)).toReal)) =ᶠ[atTop]
      (fun n : ℕ =>
        (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n+t)).toReal/
          (pureCriticalPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal) := by
    filter_upwards [hEdge₁,hEdge₂] with n hn₁ hn₂
    have hA := pureCriticalPhysicalIntensity_toReal_pos n p hp a ha
      h.overlap_range.1 _ hn₁
    have hB := pureCriticalPhysicalIntensity_toReal_pos n p hp a ha
      h.overlap_range.1 _ hn₂
    rw [←Real.log_div hB.ne' hA.ne',Real.exp_log (div_pos hB hA)]
  exact hExp.congr' hEq

end SlowEquilibration.SphericalMarkedWindows
